-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_100
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:26:36.188902+00:00
-- url     : https://prove2.me/submissions/48f1d584-d3e0-4476-8200-2bfa38ffe8ee

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_100
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_100 j) = true ∧ (witnessD8_100 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
