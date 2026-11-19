-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_079
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:06:10.48447+00:00
-- url     : https://prove2.me/submissions/6413e56b-499e-4d3d-85c2-9d86b8261260

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_079
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_079 j) = true ∧ (witnessP9_079 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
