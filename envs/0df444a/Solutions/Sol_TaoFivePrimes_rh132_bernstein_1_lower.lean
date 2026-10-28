-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_1_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:11:14.896772+00:00
-- url     : https://prove2.me/submissions/3936a4a6-d7ca-4585-a295-127fdbc36119

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag133p2To133p8
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 12, ∀ j : Fin 23,
    (11:ℚ)≤RH132BernsteinImag133p2To133p8.b i j := by
  decide +kernel
