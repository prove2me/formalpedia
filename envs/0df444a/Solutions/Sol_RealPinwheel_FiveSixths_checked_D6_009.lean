-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:39.466004+00:00
-- url     : https://prove2.me/submissions/42d19b96-808e-4d03-b679-b7d1f061a437

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_009
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessD6_009 j) = true ∧ (witnessD6_009 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
