-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_221
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:13:58.653264+00:00
-- url     : https://prove2.me/submissions/18a7b242-f0b6-4302-9f54-e4ca444608a6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_221
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_221 j) = true ∧ (witnessD8_221 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
