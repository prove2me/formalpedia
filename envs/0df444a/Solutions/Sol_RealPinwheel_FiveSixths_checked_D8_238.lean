-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_238
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:29:02.840277+00:00
-- url     : https://prove2.me/submissions/2187df9f-a671-4001-9e04-7ad6f6ce5e7c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_238
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessD8_238 j) = true ∧ (witnessD8_238 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
