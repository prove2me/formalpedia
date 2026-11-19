-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_136
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:58:21.833034+00:00
-- url     : https://prove2.me/submissions/b9b4f4e0-a637-443d-aeb0-24b4337b20f6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_136
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_136 j) = true ∧ (witnessD8_136 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
