-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_109
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:08.524459+00:00
-- url     : https://prove2.me/submissions/6b6c921a-77f8-49a0-81e8-b83f83708656

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_109
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_109 j) = true ∧ (witnessD8_109 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
