-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:07:51.363253+00:00
-- url     : https://prove2.me/submissions/4d869125-d41b-441e-b9bb-0b60b0e2d6ac

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_003
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD6_003 j) = true ∧ (witnessD6_003 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
