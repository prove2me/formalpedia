-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:40:59.617869+00:00
-- url     : https://prove2.me/submissions/bfea8d3f-52ed-4397-8679-e0c9de7feb98

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_011
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 39, witnessCheck (witnessD6_011 j) = true ∧ (witnessD6_011 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
