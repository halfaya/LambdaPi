{-# LANGUAGE UnicodeSyntax, GADTSyntax, ExplicitForAll #-}

module LambdaPi where

-------
-- Types and terms

-- inferable term
data ITerm where
  Ann   ∷ CTerm → Type → ITerm
  Bound ∷ Int   → ITerm
  Free  ∷ Name  → ITerm
  (:@:) ∷ ITerm → CTerm → ITerm
  deriving (Show, Eq)

-- checkable term
data CTerm where
  Inf ∷ ITerm → CTerm
  Lam ∷ CTerm → CTerm
  deriving (Show, Eq)

data Name where
  Global ∷ String → Name
  Local  ∷ Int    → Name
  Quote  ∷ Int    → Name
  deriving (Show, Eq)

data Type where
  TFree ∷ Name → Type
  Fun   ∷ Type → Type → Type
  deriving (Show, Eq)

data Value where
  VLam     ∷ (Value → Value) → Value
  VNeutral ∷ Neutral → Value

data Neutral where
  NFree ∷ Name    → Neutral
  NApp  ∷ Neutral → Value → Neutral

vfree ∷ Name → Value
vfree = VNeutral . NFree

-------
-- Big step evaluation

type Env = [Value]

iEval ∷ Env → ITerm → Value
iEval e t = case t of
  Ann   ct _ → cEval e ct
  Bound i    → e !! i
  Free  n    → vfree n
  u :@: v    → case iEval e u of
                 VLam f     → f (cEval e v)
                 VNeutral n → VNeutral (NApp n (cEval e v))

cEval ∷ Env → CTerm → Value
cEval e t = case t of
  Inf it → iEval e it
  Lam ct → VLam (\x → cEval (x : e) ct)
  
-------
-- Contexts

data Kind where
  Star ∷ Kind
  deriving Show

data Info where
  HasKind ∷ Kind → Info
  HasType ∷ Type → Info
  deriving Show

type Context = [(Name, Info)]

-------
-- Type checking

type Result α = Either String α

throwError ∷ String → Result α
throwError = Left

ckind ∷ Context → Type → Kind → Result ()
ckind γ t Star = case t of
  TFree n   → case lookup n γ of
                Just (HasKind Star) → Right ()
                _                   → throwError $ concat [show t, " has no kind in " , show γ]
  Fun t1 t2 → ckind γ t1 Star >> ckind γ t2 Star

itype0 ∷ Context → ITerm → Result Type
itype0 = itype 0

itype ∷ Int → Context → ITerm → Result Type
itype i γ term = case term of
  Ann _ t   → Right t
  Bound k   → throwError $ concat [show term, " is a bound variable in itype"]
  Free  n   → case lookup n γ of
                  Just (HasType t) → Right t
                  _                → throwError $ concat [show term, " has no type in " , show γ]
  t1 :@: t2 → itype i γ t1 >>= (\t → case t of
                                       Fun a b → ctype i γ a t2 >> Right b)

ctype ∷ Int → Context → Type → CTerm → Result ()
ctype i γ τ term = case term of
  Inf t → case itype i γ t of
            Right a | a == τ    → return ()
            Right a | otherwise → throwError $ concat [show term, " of inferred type ",
                                                       show a, " does not match expected type ", show τ]
            Left  s             → Left s                                            
  Lam t → case τ of
    Fun t1 t2 → ctype (i + 1) ((Local i, HasType t1) : γ) t2 (csubst 0 (Free (Local i)) t)
    _         → throwError $ concat [show term, " does not have expected type ", show τ]

isubst ∷ Int → ITerm → ITerm → ITerm
isubst i r term = case term of
  Ann t a   → Ann (csubst i r t) a
  Bound k   → if i == k then r else Bound k
  Free  n   → Free n
  t1 :@: t2 → (isubst i r t1) :@: (csubst i r t2)

csubst ∷ Int → ITerm → CTerm → CTerm
csubst i r term = case term of
  Inf t → Inf $ isubst i r t
  Lam t → Lam $ csubst (i + i) r t
  
-------
-- Quote

quote0 ∷ Value → CTerm
quote0 = quote 0

quote ∷ Int → Value → CTerm
quote i val = case val of
  VLam f     → Lam (quote (i + 1) (f (vfree (Quote i))))
  VNeutral n → Inf $ quoteNeutral i n

quoteNeutral ∷ Int → Neutral → ITerm
quoteNeutral i (NFree n)   = Free n
quoteNeutral i (NApp  n v) = quoteNeutral i n :@: quote i v
