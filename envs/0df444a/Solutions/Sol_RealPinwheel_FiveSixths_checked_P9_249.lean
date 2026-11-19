-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_249
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:04:06.806945+00:00
-- url     : https://prove2.me/submissions/858c5ccf-db1b-465a-98c6-99ff5a00da9c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_249
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 32, witnessCheck (witnessP9_249 j) = true ∧ (witnessP9_249 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
