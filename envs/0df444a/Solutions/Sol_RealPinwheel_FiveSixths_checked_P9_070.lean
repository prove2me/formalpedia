-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_070
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:57:20.156027+00:00
-- url     : https://prove2.me/submissions/0561af90-1892-4554-bf28-f04830e4785f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_070
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_070 j) = true ∧ (witnessP9_070 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
