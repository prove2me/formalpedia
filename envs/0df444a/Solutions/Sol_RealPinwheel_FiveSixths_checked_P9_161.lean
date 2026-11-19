-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_161
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:02:23.279789+00:00
-- url     : https://prove2.me/submissions/8958577e-e4ee-4820-b2c7-3e1dbb4d4d1b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_161
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_161 j) = true ∧ (witnessP9_161 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
