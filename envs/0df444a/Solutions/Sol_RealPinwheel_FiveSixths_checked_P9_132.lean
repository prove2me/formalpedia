-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_132
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:15:48.821676+00:00
-- url     : https://prove2.me/submissions/7d36356d-b5da-491d-9203-a7925181dcd0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_132
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_132 j) = true ∧ (witnessP9_132 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
