-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_084
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:23.352247+00:00
-- url     : https://prove2.me/submissions/9702c27b-4c8f-4eb9-8335-5da8593a31c5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_084
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_084 j) = true ∧ (witnessD8_084 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
