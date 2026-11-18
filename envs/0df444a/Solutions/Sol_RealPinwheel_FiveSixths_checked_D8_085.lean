-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_085
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:56.63606+00:00
-- url     : https://prove2.me/submissions/343209ec-c2d1-4ffd-a02c-d14887c3c6f8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_085
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_085 j) = true ∧ (witnessD8_085 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
