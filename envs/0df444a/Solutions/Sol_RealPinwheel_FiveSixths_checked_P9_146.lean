-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_146
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:40:48.178418+00:00
-- url     : https://prove2.me/submissions/a8afb396-281a-43aa-a411-5804e56b4f09

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_146
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_146 j) = true ∧ (witnessP9_146 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
