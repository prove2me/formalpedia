-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_078
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:42.967308+00:00
-- url     : https://prove2.me/submissions/94919b2f-c672-4357-8afe-f7677f4b9b60

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_078
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_078 j) = true ∧ (witnessP9_078 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
