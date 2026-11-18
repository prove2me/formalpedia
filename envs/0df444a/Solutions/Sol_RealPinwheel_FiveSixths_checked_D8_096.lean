-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_096
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:04.202973+00:00
-- url     : https://prove2.me/submissions/1fe8bb41-6795-47d8-a28d-eba93c83e8d5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_096
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_096 j) = true ∧ (witnessD8_096 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
