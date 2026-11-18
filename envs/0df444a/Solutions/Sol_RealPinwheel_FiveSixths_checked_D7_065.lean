-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_065
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:07.068196+00:00
-- url     : https://prove2.me/submissions/1792abf4-0280-41d5-bbd7-ba7738d4be08

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_065
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessD7_065 j) = true ∧ (witnessD7_065 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
