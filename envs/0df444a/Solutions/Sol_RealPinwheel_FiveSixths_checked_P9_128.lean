-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_128
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:12:40.520196+00:00
-- url     : https://prove2.me/submissions/02b5d1dc-4804-41a7-9ca8-3e53e52bc2fa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_128
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_128 j) = true ∧ (witnessP9_128 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
