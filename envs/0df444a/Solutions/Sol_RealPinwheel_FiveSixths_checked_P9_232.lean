-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_232
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:48:56.646987+00:00
-- url     : https://prove2.me/submissions/875b7ec4-bcb9-468f-9949-d7423a7f8f94

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_232
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_232 j) = true ∧ (witnessP9_232 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
