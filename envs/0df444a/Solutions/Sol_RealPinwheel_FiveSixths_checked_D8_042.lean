-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_042
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:51:25.078182+00:00
-- url     : https://prove2.me/submissions/b054a0d3-984f-42b7-a660-0f36a5b95312

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_042
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_042 j) = true ∧ (witnessD8_042 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
