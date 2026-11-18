-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_073
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:51.504938+00:00
-- url     : https://prove2.me/submissions/a67e97df-f5bd-48f4-b8df-09d089dacf72

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_073
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_073 j) = true ∧ (witnessD8_073 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
