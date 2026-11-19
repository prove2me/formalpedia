-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_123
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:08:42.592674+00:00
-- url     : https://prove2.me/submissions/cd558b05-240c-46ad-9697-85b9dd1f07f2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_123
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_123 j) = true ∧ (witnessP9_123 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
