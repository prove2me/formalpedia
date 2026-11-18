-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_020
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:48.36184+00:00
-- url     : https://prove2.me/submissions/c0a69a95-d2e9-4196-8409-26c31e5d6803

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_020
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_020 j) = true ∧ (witnessP9_020 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
