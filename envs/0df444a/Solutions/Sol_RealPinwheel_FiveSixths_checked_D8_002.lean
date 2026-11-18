-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:36:57.807019+00:00
-- url     : https://prove2.me/submissions/d718f305-3811-441a-8a47-01118d5a63f2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_002
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessD8_002 j) = true ∧ (witnessD8_002 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
