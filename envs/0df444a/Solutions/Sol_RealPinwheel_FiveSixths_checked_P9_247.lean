-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_247
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:02:25.45667+00:00
-- url     : https://prove2.me/submissions/6cba856b-ecfd-45f5-9200-7a11b6db9512

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_247
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_247 j) = true ∧ (witnessP9_247 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
