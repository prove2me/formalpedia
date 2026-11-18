-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_046
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:48.811331+00:00
-- url     : https://prove2.me/submissions/84137585-215f-4bf2-9bf1-6a7965f20cd0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_046
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_046 j) = true ∧ (witnessP9_046 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
