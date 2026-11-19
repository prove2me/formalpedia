-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_101
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:35:03.222088+00:00
-- url     : https://prove2.me/submissions/58e9b3f7-a3cc-40e8-a683-e26c289a8f3c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_101
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_101 j) = true ∧ (witnessP9_101 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
