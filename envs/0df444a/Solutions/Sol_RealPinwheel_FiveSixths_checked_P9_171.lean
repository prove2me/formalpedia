-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_171
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:06:39.803218+00:00
-- url     : https://prove2.me/submissions/badf18d3-aad0-4db8-b879-1dd4712299e9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_171
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessP9_171 j) = true ∧ (witnessP9_171 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
