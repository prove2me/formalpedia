-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_2_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:41:02.277999+00:00
-- url     : https://prove2.me/submissions/6f7d6982-fe4b-4cdc-b0ac-32dff0b6ade0

import Definitions.Def_TaoFivePrimes_RH132BernsteinNegative133p8To134p4
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 12, ∀ j : Fin 23,
    (6:ℚ)≤RH132BernsteinNegative133p8To134p4.b i j := by
  decide +kernel
