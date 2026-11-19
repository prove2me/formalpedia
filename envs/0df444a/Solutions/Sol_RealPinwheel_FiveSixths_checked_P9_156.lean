-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_156
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:53.220435+00:00
-- url     : https://prove2.me/submissions/97b34a66-634c-407e-ad58-e511821766f8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_156
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessP9_156 j) = true ∧ (witnessP9_156 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
