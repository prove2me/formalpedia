-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_067
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:23.609956+00:00
-- url     : https://prove2.me/submissions/95ac7693-69a0-4a7c-a38f-810121f378f8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_067
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_067 j) = true ∧ (witnessD8_067 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
