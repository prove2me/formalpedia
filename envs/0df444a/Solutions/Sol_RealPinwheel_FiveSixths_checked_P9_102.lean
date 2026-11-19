-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_102
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:35:00.35091+00:00
-- url     : https://prove2.me/submissions/1e5391cc-3b59-487a-a6e7-1531c22a2627

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_102
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_102 j) = true ∧ (witnessP9_102 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
