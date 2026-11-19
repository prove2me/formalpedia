-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_191
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:42:02.320461+00:00
-- url     : https://prove2.me/submissions/570c8771-8059-4f31-8360-4ec5c0774ea8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_191
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessD8_191 j) = true ∧ (witnessD8_191 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
