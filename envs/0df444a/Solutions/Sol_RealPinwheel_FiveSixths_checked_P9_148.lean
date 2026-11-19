-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_148
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:47:01.168186+00:00
-- url     : https://prove2.me/submissions/1a23bc2e-06bb-485f-be2c-a7a7b1f58e92

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_148
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_148 j) = true ∧ (witnessP9_148 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
