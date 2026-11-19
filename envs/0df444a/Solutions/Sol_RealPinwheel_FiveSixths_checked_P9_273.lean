-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_273
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:16:23.040106+00:00
-- url     : https://prove2.me/submissions/8d622db5-fa7f-4842-99db-045572230e60

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_273
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 39, witnessCheck (witnessP9_273 j) = true ∧ (witnessP9_273 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
