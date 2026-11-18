-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_059
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:02.882528+00:00
-- url     : https://prove2.me/submissions/dfac2d72-c1ab-40a7-8c0b-d2746bb304f7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_059
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 32, witnessCheck (witnessD7_059 j) = true ∧ (witnessD7_059 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
