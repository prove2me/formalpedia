-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_324
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:46:14.299253+00:00
-- url     : https://prove2.me/submissions/0280f27b-c517-44f2-bd0f-97c1a52aa292

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_324
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 75, witnessCheck (witnessP9_324 j) = true ∧ (witnessP9_324 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
