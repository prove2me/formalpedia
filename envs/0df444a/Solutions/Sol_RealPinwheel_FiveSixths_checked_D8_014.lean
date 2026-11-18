-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_014
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:03.712274+00:00
-- url     : https://prove2.me/submissions/530e90c0-e78c-4dc3-aee4-2defc478dcb4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_014
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD8_014 j) = true ∧ (witnessD8_014 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
