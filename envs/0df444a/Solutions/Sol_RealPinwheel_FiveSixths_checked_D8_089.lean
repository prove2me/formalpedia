-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_089
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:35.754965+00:00
-- url     : https://prove2.me/submissions/218beaaf-f554-4ccb-a9b0-13c708363ac6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_089
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_089 j) = true ∧ (witnessD8_089 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
