-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_213
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:01:07.401501+00:00
-- url     : https://prove2.me/submissions/9bdb5056-57d9-4fa4-b9c4-e73ddc51ffed

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_213
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessD8_213 j) = true ∧ (witnessD8_213 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
