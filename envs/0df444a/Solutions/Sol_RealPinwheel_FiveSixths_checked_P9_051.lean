-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_051
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:23:29.932374+00:00
-- url     : https://prove2.me/submissions/bda8eb68-0ad0-40b0-9c79-aa50e004738b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_051
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_051 j) = true ∧ (witnessP9_051 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
