-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_079
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:10:27.931884+00:00
-- url     : https://prove2.me/submissions/fbad4158-5327-4877-a48f-e9c0ebcc8b58

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_079
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_079 j) = true ∧ (witnessD8_079 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
