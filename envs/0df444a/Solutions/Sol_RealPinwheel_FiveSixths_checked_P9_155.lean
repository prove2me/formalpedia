-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_155
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:59:36.514082+00:00
-- url     : https://prove2.me/submissions/a07629b0-afb0-4c92-9f9f-1cd1eeb1f9aa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_155
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessP9_155 j) = true ∧ (witnessP9_155 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
