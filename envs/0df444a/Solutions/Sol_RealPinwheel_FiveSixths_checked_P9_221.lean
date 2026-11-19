-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_221
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:41:57.146192+00:00
-- url     : https://prove2.me/submissions/345202e0-e113-482e-adcc-57daa74e0ab9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_221
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_221 j) = true ∧ (witnessP9_221 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
