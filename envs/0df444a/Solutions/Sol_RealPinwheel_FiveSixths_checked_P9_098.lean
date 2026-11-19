-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_098
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:30:28.837999+00:00
-- url     : https://prove2.me/submissions/0bc3528f-80bc-4371-a223-7e5ce364e37e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_098
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_098 j) = true ∧ (witnessP9_098 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
