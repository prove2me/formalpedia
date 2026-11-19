-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_252
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:06:02.180579+00:00
-- url     : https://prove2.me/submissions/f5865f69-f1e5-422c-95ff-e91ce3ff4d48

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_252
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessP9_252 j) = true ∧ (witnessP9_252 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
