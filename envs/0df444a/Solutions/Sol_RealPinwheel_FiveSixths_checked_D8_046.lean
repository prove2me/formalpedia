-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_046
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:38.976979+00:00
-- url     : https://prove2.me/submissions/0794a381-f616-4f12-9121-2400268ad9c4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_046
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_046 j) = true ∧ (witnessD8_046 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
