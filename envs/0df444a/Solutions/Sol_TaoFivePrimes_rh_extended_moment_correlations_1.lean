-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_correlations_1
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:09:18.458374+00:00
-- url     : https://prove2.me/submissions/ad2aac1b-abd7-414f-b87d-62a8c9d4fa3f

import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations1
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 4, ∀ m : Fin 184,
    RHNextMomentInteger.correlation (4+i.val) m.val =
      ((TaoFivePrimes_RHExtendedMomentCorrelations1.getD i.val []).getD m.val 0) := by
  intro i
  fin_cases i <;> decide +kernel
