-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_240
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:51:10.223861+00:00
-- url     : https://prove2.me/submissions/7b8a6a0c-6b62-4dc1-8815-ecfe154d43a9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_240
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 30, witnessCheck (witnessP9_240 j) = true ∧ (witnessP9_240 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
