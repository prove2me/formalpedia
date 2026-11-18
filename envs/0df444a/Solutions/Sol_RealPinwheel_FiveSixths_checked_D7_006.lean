-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_006
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:21:35.746208+00:00
-- url     : https://prove2.me/submissions/6ae48ea4-ce94-4d76-a4ee-a33f218d8f57

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_006
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD7_006 j) = true ∧ (witnessD7_006 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
