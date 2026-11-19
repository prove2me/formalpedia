-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_142
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:36:34.689454+00:00
-- url     : https://prove2.me/submissions/c889ec85-009d-4d3c-8e4b-9c0a93a88949

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_142
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_142 j) = true ∧ (witnessP9_142 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
