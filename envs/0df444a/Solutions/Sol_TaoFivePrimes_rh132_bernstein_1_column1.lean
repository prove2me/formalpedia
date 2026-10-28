-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_1_column1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:10:53.843887+00:00
-- url     : https://prove2.me/submissions/9fe30616-f379-40a3-b4f0-7d0dded08ade

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 3, ∀ j : Fin 23,
    RH132BernsteinImag133p2To133p8.b ⟨3+i.val, by omega⟩ j = RH132BernsteinImag133p2To133p8.transform 11 (fun u => RH132BernsteinImag133p2To133p8.r u j) ⟨3+i.val, by omega⟩ := by
  decide +kernel
