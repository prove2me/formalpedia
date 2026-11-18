-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_078
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:12:33.888196+00:00
-- url     : https://prove2.me/submissions/2578844d-afc6-4bb3-b99c-0d4ba941cf0d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_078
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_078 j) = true ∧ (witnessD8_078 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
