-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_023
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:51.39507+00:00
-- url     : https://prove2.me/submissions/97fd520c-1958-4f1e-b058-806393fa2add

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_023
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_023 j) = true ∧ (witnessD8_023 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
