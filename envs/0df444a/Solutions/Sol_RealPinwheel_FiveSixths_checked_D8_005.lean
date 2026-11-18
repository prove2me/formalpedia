-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:18:20.681186+00:00
-- url     : https://prove2.me/submissions/fb725813-5b52-4c15-b1a0-bf79086604e7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_005
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessD8_005 j) = true ∧ (witnessD8_005 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
