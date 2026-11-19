-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_170
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:27:39.826492+00:00
-- url     : https://prove2.me/submissions/342898e2-eb2c-4027-b48a-a35802f092b3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_170
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_170 j) = true ∧ (witnessD8_170 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
