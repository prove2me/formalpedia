-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_125
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:10:57.484474+00:00
-- url     : https://prove2.me/submissions/5bc287ee-f8da-4e9f-a36a-456abd6b6e79

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_125
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_125 j) = true ∧ (witnessP9_125 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
