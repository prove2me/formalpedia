-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_193
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:44:29.145767+00:00
-- url     : https://prove2.me/submissions/b0d4b910-1f0f-4c4d-945f-f8f31d2f65f4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_193
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_193 j) = true ∧ (witnessD8_193 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
