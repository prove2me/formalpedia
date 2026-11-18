-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_046
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:11.527586+00:00
-- url     : https://prove2.me/submissions/eac09461-11e3-4c4b-ad77-f5a7761dc4b3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_046
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD7_046 j) = true ∧ (witnessD7_046 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
