-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_200
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:50:57.897711+00:00
-- url     : https://prove2.me/submissions/19b1cf2c-4413-49e5-81fa-f8790d0edf14

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_200
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD8_200 j) = true ∧ (witnessD8_200 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
