-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_109
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:46:34.297645+00:00
-- url     : https://prove2.me/submissions/c50d6ae2-8b17-4362-8213-b83e605d5e66

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_109
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_109 j) = true ∧ (witnessP9_109 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
