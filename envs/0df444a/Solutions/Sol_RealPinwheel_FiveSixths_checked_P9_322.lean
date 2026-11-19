-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_322
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:46:09.825537+00:00
-- url     : https://prove2.me/submissions/370c517c-837b-46bb-bf2c-48891284bb9d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_322
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 72, witnessCheck (witnessP9_322 j) = true ∧ (witnessP9_322 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
