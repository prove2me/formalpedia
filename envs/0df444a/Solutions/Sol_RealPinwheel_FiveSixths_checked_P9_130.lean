-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_130
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:15:46.777633+00:00
-- url     : https://prove2.me/submissions/ed979f10-71f5-497e-bfb3-b59282aec901

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_130
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_130 j) = true ∧ (witnessP9_130 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
