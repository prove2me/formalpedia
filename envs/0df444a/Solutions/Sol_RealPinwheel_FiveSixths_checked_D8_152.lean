-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_152
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:15:42.67086+00:00
-- url     : https://prove2.me/submissions/b7499e8e-4899-4fcb-af28-7b0b99b3d36e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_152
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_152 j) = true ∧ (witnessD8_152 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
