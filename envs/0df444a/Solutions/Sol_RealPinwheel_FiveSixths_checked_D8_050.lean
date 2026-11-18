-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_050
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:44.571333+00:00
-- url     : https://prove2.me/submissions/a5bc0abb-8445-4979-9e83-733db80fdee7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_050
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_050 j) = true ∧ (witnessD8_050 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
