-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_207
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:01.265232+00:00
-- url     : https://prove2.me/submissions/a0c6c4f8-ce6d-4368-8947-f5696c426067

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_207
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 24, witnessCheck (witnessP9_207 j) = true ∧ (witnessP9_207 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
