-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_036
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:58.887296+00:00
-- url     : https://prove2.me/submissions/d1c5fa48-6a8b-44c9-b51a-b632defa7020

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_036
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD7_036 j) = true ∧ (witnessD7_036 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
