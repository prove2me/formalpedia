-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_332
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:53:09.682731+00:00
-- url     : https://prove2.me/submissions/23559ff8-f47a-4eac-9420-ca7235763116

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_332
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 99, witnessCheck (witnessP9_332 j) = true ∧ (witnessP9_332 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
