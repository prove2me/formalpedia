-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_210
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:59:20.797699+00:00
-- url     : https://prove2.me/submissions/8d602ba8-e289-426d-9e6a-b23d19f1273a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_210
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD8_210 j) = true ∧ (witnessD8_210 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
