-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_062
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:41.435117+00:00
-- url     : https://prove2.me/submissions/1faeed12-c4f6-4e55-b7bc-f6af030ada75

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_062
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_062 j) = true ∧ (witnessP9_062 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
