-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_185
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:43.74352+00:00
-- url     : https://prove2.me/submissions/77e1c1c0-38a8-41d9-8b17-cedcb055f547

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_185
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessP9_185 j) = true ∧ (witnessP9_185 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
