-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_311
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:41:10.627178+00:00
-- url     : https://prove2.me/submissions/4df2c1eb-b1a9-41e0-bfed-3f5167d69b96

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_311
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 57, witnessCheck (witnessP9_311 j) = true ∧ (witnessP9_311 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
