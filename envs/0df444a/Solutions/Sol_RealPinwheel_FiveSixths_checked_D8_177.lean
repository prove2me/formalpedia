-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_177
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:32:12.328546+00:00
-- url     : https://prove2.me/submissions/67d959c3-170c-444b-89c1-5fc8dc50c131

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_177
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_177 j) = true ∧ (witnessD8_177 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
