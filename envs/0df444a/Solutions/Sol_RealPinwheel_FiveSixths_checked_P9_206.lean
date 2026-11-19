-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_206
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:49.213697+00:00
-- url     : https://prove2.me/submissions/6512ea47-54f8-4aed-8a7c-46599143a901

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_206
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_206 j) = true ∧ (witnessP9_206 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
