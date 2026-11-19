-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_075
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:02:08.840468+00:00
-- url     : https://prove2.me/submissions/96f301da-bc3f-4367-8c25-d3051137e52c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_075
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_075 j) = true ∧ (witnessP9_075 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
