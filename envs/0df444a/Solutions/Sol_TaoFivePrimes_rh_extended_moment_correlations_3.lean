-- Prove2me | solution 1 for TaoFivePrimes.rh_extended_moment_correlations_3
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T19:10:25.36597+00:00
-- url     : https://prove2.me/submissions/d227e819-6d62-44e7-a1fc-e97f5f217067

import Definitions.Def_TaoFivePrimes_RHExtendedMomentIntegerRule
import Definitions.Def_TaoFivePrimes_RHExtendedMomentCorrelations3
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

theorem solution : ∀ i : Fin 4, ∀ m : Fin 184,
    RHNextMomentInteger.correlation (12+i.val) m.val =
      ((TaoFivePrimes_RHExtendedMomentCorrelations3.getD i.val []).getD m.val 0) := by
  intro i
  fin_cases i <;> decide +kernel
