-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_063
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:01:40.811107+00:00
-- url     : https://prove2.me/submissions/a55d2976-2d68-4e4b-b8ff-3e8c245e992c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_063
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_063 j) = true ∧ (witnessD8_063 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
