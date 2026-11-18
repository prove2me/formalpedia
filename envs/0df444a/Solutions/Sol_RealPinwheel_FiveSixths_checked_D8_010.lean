-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_010
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:43.843259+00:00
-- url     : https://prove2.me/submissions/8ea64bb1-d64d-41d7-b631-87cfdc7faaa9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_010
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD8_010 j) = true ∧ (witnessD8_010 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
