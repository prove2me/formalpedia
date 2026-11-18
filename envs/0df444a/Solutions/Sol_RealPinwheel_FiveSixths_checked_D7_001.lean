-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:15:40.993715+00:00
-- url     : https://prove2.me/submissions/3086be8c-d4f0-46a8-a8f3-b2c646dc62d0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_001
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD7_001 j) = true ∧ (witnessD7_001 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
