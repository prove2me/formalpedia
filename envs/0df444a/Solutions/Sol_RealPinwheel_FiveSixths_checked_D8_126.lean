-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_126
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:55:04.167433+00:00
-- url     : https://prove2.me/submissions/3a1d6150-fa51-4823-9255-c7ff32df2673

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_126
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_126 j) = true ∧ (witnessD8_126 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
