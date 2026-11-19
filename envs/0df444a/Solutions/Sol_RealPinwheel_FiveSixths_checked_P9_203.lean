-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_203
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:14.293475+00:00
-- url     : https://prove2.me/submissions/9d125b5b-f5f6-45ec-a55d-2ac4cc24c374

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_203
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_203 j) = true ∧ (witnessP9_203 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
