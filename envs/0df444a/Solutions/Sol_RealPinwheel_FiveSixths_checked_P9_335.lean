-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_335
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:54:43.105455+00:00
-- url     : https://prove2.me/submissions/e1ef0feb-5786-47e2-9c5b-b79e7e6822d7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_335
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 131, witnessCheck (witnessP9_335 j) = true ∧ (witnessP9_335 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
