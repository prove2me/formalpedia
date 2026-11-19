-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_300
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:34:39.515068+00:00
-- url     : https://prove2.me/submissions/1103a7bb-2d82-4b20-af46-cf3188107496

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_300
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 50, witnessCheck (witnessP9_300 j) = true ∧ (witnessP9_300 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
