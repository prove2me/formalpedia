-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_066
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:06:15.98655+00:00
-- url     : https://prove2.me/submissions/9bcfa653-6b1c-4117-9d43-3c45c991ffd6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_066
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_066 j) = true ∧ (witnessD8_066 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
