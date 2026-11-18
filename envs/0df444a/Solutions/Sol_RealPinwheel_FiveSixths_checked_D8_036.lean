-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_036
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:56.253707+00:00
-- url     : https://prove2.me/submissions/eeb4e779-d83c-4e0c-8a36-66c4a3ec42a6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_036
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_036 j) = true ∧ (witnessD8_036 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
