-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_024
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:32.580488+00:00
-- url     : https://prove2.me/submissions/6d646bc4-015d-4fd8-a3d2-79526afe1c61

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_024
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_024 j) = true ∧ (witnessD8_024 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
