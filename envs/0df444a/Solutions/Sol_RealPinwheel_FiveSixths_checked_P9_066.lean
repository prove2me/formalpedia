-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_066
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:46:34.214001+00:00
-- url     : https://prove2.me/submissions/a0a70c66-25d1-4e57-83f4-f90533adbb69

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_066
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_066 j) = true ∧ (witnessP9_066 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
