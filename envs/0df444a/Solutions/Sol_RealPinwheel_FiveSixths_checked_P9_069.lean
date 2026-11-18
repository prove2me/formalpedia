-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_069
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:48:08.776304+00:00
-- url     : https://prove2.me/submissions/6c930c61-4e4d-40de-bf13-c2f95ececb03

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_069
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_069 j) = true ∧ (witnessP9_069 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
