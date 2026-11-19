-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_285
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:24:09.301266+00:00
-- url     : https://prove2.me/submissions/020023d4-7182-414b-9795-df0f774412d1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_285
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 44, witnessCheck (witnessP9_285 j) = true ∧ (witnessP9_285 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
