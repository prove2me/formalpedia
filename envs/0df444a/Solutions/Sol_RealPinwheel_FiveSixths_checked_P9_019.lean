-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_019
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:43.059317+00:00
-- url     : https://prove2.me/submissions/e3e8d3b3-c55b-418a-830b-a6d3b25fe54c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_019
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_019 j) = true ∧ (witnessP9_019 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
