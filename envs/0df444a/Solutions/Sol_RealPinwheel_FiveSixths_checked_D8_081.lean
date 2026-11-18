-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_081
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:13:32.306549+00:00
-- url     : https://prove2.me/submissions/568ad06d-25be-4e95-b7e4-32c97e507156

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_081
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_081 j) = true ∧ (witnessD8_081 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
