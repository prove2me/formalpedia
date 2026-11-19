-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_114
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:50:49.316975+00:00
-- url     : https://prove2.me/submissions/3c4b5d7e-8a2f-42d7-b15f-6e2f8dc15c7d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_114
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_114 j) = true ∧ (witnessP9_114 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
