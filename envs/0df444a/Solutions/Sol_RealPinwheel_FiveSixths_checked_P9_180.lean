-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_180
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:42.789196+00:00
-- url     : https://prove2.me/submissions/09b655aa-babf-4711-ad64-2fcc151d0e93

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_180
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_180 j) = true ∧ (witnessP9_180 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
