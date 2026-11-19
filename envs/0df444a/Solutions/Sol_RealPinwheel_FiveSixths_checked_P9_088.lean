-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_088
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:21:03.895214+00:00
-- url     : https://prove2.me/submissions/b3b493d9-d585-437b-8d57-d3c29f77b1f5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_088
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_088 j) = true ∧ (witnessP9_088 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
