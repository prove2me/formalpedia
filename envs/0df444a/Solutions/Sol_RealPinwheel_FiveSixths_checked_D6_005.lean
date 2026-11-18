-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:16:38.768289+00:00
-- url     : https://prove2.me/submissions/bd91fd25-f344-464f-b061-6729075f7cbb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_005
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessD6_005 j) = true ∧ (witnessD6_005 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
