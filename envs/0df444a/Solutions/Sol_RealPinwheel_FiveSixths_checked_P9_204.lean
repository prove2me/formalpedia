-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_204
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:26.608369+00:00
-- url     : https://prove2.me/submissions/18e2901b-29e7-4221-9e67-a20788d9d9f4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_204
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_204 j) = true ∧ (witnessP9_204 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
