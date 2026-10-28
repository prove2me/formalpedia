-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_correlations_2
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:09:18.672995+00:00
-- url     : https://prove2.me/submissions/9aff8361-90ae-4ec8-959f-72255f793d5a

import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 4, ∀ m : Fin 184,
    RHNextMomentInteger.correlation (8+i.val) m.val =
      ((TaoFivePrimes_RHExtendedMomentCorrelations2.getD i.val []).getD m.val 0) := by
  intro i
  fin_cases i <;> decide +kernel
