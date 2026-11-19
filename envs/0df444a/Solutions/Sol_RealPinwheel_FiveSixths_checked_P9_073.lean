-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_073
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:02:38.364202+00:00
-- url     : https://prove2.me/submissions/65caf69a-785c-487a-aa55-d9c8f5148c18

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_073
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_073 j) = true ∧ (witnessP9_073 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
