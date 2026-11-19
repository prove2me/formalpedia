-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_150
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:14:46.594601+00:00
-- url     : https://prove2.me/submissions/1615942e-e13e-4876-bdea-88a9e13849ef

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_150
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_150 j) = true ∧ (witnessD8_150 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
