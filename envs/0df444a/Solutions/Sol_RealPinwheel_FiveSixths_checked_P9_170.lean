-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_170
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:03:14.958206+00:00
-- url     : https://prove2.me/submissions/33b606b0-f9a5-46e0-8a67-fa71f271d2fe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_170
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_170 j) = true ∧ (witnessP9_170 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
