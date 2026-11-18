-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_019
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:47.85504+00:00
-- url     : https://prove2.me/submissions/b8f1fe56-94b7-4dda-aa91-d7668f33adff

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_019
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD7_019 j) = true ∧ (witnessD7_019 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
