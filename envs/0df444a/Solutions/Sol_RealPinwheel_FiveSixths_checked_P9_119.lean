-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_119
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:02:43.355054+00:00
-- url     : https://prove2.me/submissions/169e9559-01ac-45fd-90c7-d7adcbec9d1b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_119
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_119 j) = true ∧ (witnessP9_119 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
