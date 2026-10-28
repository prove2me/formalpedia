-- Prove2me | solution 1 for TaoFivePrimes.rh132_bernstein_3_lower
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T00:43:11.589545+00:00
-- url     : https://prove2.me/submissions/d20de522-1398-464e-9037-ac75d8302ead

import Definitions.Def_TaoFivePrimes_RH132BernsteinImag134p4To135
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 12, ∀ j : Fin 23,
    (14:ℚ)≤RH132BernsteinImag134p4To135.b i j := by
  decide +kernel
