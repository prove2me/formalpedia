-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_014
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:35.447962+00:00
-- url     : https://prove2.me/submissions/4aaca5ef-cc1d-47e0-9f0a-f22f3833252b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_014
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 52, witnessCheck (witnessD6_014 j) = true ∧ (witnessD6_014 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
