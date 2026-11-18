-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_120
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:48:11.937777+00:00
-- url     : https://prove2.me/submissions/da22f296-1f64-4f3d-8530-99ff61a47aeb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_120
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_120 j) = true ∧ (witnessD8_120 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
