-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_255
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:06:26.584087+00:00
-- url     : https://prove2.me/submissions/8d55c9c9-8193-47e4-b1f2-927227520053

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_255
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessP9_255 j) = true ∧ (witnessP9_255 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
