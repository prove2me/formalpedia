-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_199
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:36.498208+00:00
-- url     : https://prove2.me/submissions/9c04343f-9263-47e7-bc09-4e9c66faf6e4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_199
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_199 j) = true ∧ (witnessP9_199 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
