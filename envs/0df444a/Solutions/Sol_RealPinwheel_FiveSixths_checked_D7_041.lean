-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_041
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:34.362759+00:00
-- url     : https://prove2.me/submissions/2c18911a-7ff7-4c86-8b49-1272c1ab60c1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_041
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD7_041 j) = true ∧ (witnessD7_041 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
