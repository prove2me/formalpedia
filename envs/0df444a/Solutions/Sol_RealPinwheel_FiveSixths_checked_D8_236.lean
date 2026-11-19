-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_236
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:25:16.378468+00:00
-- url     : https://prove2.me/submissions/6be3daa3-d2a7-491e-8fca-1c5d6a6cefe5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_236
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessD8_236 j) = true ∧ (witnessD8_236 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
