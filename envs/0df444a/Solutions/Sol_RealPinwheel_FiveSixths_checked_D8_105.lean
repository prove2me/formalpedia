-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_105
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:37:31.382979+00:00
-- url     : https://prove2.me/submissions/7ec18274-5f41-4c96-af3d-577a5acff0ac

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_105
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_105 j) = true ∧ (witnessD8_105 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
