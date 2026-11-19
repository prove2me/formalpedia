-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_235
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:01.120245+00:00
-- url     : https://prove2.me/submissions/468482f4-fbf7-4fa7-a734-80d82dd7ef81

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_235
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_235 j) = true ∧ (witnessP9_235 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
