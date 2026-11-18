-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_049
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:51.317925+00:00
-- url     : https://prove2.me/submissions/d7dfdc7a-b907-4657-a9be-c36b6e51f9b2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_049
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD7_049 j) = true ∧ (witnessD7_049 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
