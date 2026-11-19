-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_176
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:31:35.533907+00:00
-- url     : https://prove2.me/submissions/08a37782-c8bb-4520-875c-a5375ba2660d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_176
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_176 j) = true ∧ (witnessD8_176 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
