-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:19:52.796887+00:00
-- url     : https://prove2.me/submissions/9cdbff78-7cc8-4dc4-afda-e08f3a362515

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_008
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD7_008 j) = true ∧ (witnessD7_008 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
