-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_220
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:03.8712+00:00
-- url     : https://prove2.me/submissions/45980333-8dff-4307-b22f-184311a9a527

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_220
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD8_220 j) = true ∧ (witnessD8_220 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
