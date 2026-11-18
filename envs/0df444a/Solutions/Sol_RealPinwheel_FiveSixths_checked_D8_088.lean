-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_088
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:15.365693+00:00
-- url     : https://prove2.me/submissions/bc7daee5-cbb8-4859-925e-61416a8cffae

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_088
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_088 j) = true ∧ (witnessD8_088 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
