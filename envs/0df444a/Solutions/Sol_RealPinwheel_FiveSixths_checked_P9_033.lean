-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_033
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:42.346821+00:00
-- url     : https://prove2.me/submissions/16ab7eda-e7c7-4647-8c84-5d6d4d9e36c0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_033
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_033 j) = true ∧ (witnessP9_033 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
