-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_262
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:11:01.403899+00:00
-- url     : https://prove2.me/submissions/2465e529-faae-435c-9539-1a12e565edea

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_262
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessP9_262 j) = true ∧ (witnessP9_262 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
