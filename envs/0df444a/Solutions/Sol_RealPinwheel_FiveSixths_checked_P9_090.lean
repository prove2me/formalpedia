-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_090
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:23:37.808322+00:00
-- url     : https://prove2.me/submissions/770c6d11-06b0-44ba-93dc-8b66606cf69a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_090
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_090 j) = true ∧ (witnessP9_090 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
