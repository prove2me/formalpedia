-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_122
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:08:53.792295+00:00
-- url     : https://prove2.me/submissions/d8e01b86-68e3-41f2-a76e-07b2747c3607

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_122
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_122 j) = true ∧ (witnessP9_122 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
