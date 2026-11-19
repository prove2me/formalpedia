-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_243
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:56:18.368004+00:00
-- url     : https://prove2.me/submissions/54ad59ca-e433-48c7-a6ac-2adf01f3ba28

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_243
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_243 j) = true ∧ (witnessP9_243 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
