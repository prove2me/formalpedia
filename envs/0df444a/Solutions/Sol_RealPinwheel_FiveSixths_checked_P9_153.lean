-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_153
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:43.503471+00:00
-- url     : https://prove2.me/submissions/9ab4a86c-efe1-407e-adbf-2cc0b3a018bb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_153
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_153 j) = true ∧ (witnessP9_153 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
