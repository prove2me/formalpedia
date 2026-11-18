-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_042
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:18:33.684668+00:00
-- url     : https://prove2.me/submissions/68e6dbac-f879-4eb5-88bb-f043a2067bd1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_042
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_042 j) = true ∧ (witnessP9_042 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
