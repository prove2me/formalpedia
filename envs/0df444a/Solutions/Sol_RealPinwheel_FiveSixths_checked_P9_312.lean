-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_312
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:39:38.93035+00:00
-- url     : https://prove2.me/submissions/a3dae49e-ef77-488a-91f6-c9e6ef3c5705

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_312
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 58, witnessCheck (witnessP9_312 j) = true ∧ (witnessP9_312 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
