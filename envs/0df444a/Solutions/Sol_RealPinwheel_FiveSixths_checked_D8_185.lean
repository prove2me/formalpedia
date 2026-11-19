-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_185
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:37:56.557208+00:00
-- url     : https://prove2.me/submissions/7b43424e-7cd8-4a7d-8d6f-7a31a35142b4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_185
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_185 j) = true ∧ (witnessD8_185 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
