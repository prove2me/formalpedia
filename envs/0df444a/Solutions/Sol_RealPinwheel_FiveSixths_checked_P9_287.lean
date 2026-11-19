-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_287
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:24:44.715244+00:00
-- url     : https://prove2.me/submissions/8b3be025-5a8a-4058-b385-e2a71ab7c842

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_287
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 44, witnessCheck (witnessP9_287 j) = true ∧ (witnessP9_287 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
