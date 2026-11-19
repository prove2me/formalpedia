-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_198
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:32:14.717192+00:00
-- url     : https://prove2.me/submissions/7b27fa80-63f2-46a9-9503-57ffb948f1e9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_198
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_198 j) = true ∧ (witnessP9_198 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
