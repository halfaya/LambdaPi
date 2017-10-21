{-# LANGUAGE UnicodeSyntax, GADTSyntax, ExplicitForAll #-}

module Main where

import LambdaPi

fid ∷ CTerm
fid = Lam (Inf $ Bound 0)

checkFid ∷ Result ()
checkFid = ctype 0 [] (Fun (TFree (Global "a")) (TFree (Global "a"))) fid

quoteFid ∷ CTerm
quoteFid = quote0 (cEval [] fid)

quoteFid2 ∷ CTerm
quoteFid2 = quote0 (cEval [] fid)

main ∷ IO ()
main = putStrLn "hello world"
