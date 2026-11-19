-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_225
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:13:07.36022+00:00
-- url     : https://prove2.me/submissions/695a5343-6bc2-422f-b2bb-044c858fbf15

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_225
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD8_225 j) = true ∧ (witnessD8_225 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
