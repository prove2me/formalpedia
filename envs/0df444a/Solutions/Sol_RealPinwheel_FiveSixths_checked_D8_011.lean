-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:34.533715+00:00
-- url     : https://prove2.me/submissions/33d3a37f-7d98-40b4-8756-a0056a2232f2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_011
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD8_011 j) = true ∧ (witnessD8_011 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
