-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_153
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:15:33.504605+00:00
-- url     : https://prove2.me/submissions/ff97f432-44a7-4fae-a76d-a404c95e9a70

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_153
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_153 j) = true ∧ (witnessD8_153 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
