-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_026
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:30.9356+00:00
-- url     : https://prove2.me/submissions/366cd17e-c9dd-4d70-b02e-e094a9b85b6b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_026
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD7_026 j) = true ∧ (witnessD7_026 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
