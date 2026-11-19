-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_318
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:43:20.907311+00:00
-- url     : https://prove2.me/submissions/ca8ef234-ffd5-499a-b41d-d8bbcbd2dc7e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_318
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 67, witnessCheck (witnessP9_318 j) = true ∧ (witnessP9_318 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
