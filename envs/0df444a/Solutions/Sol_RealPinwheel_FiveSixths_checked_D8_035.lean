-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_035
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:46:50.645199+00:00
-- url     : https://prove2.me/submissions/747ac67d-3c4e-4f15-9a88-eab10ef3cca7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_035
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_035 j) = true ∧ (witnessD8_035 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
