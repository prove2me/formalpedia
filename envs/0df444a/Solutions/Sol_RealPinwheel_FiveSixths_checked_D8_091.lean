-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_091
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:39.196463+00:00
-- url     : https://prove2.me/submissions/ac369cba-0e20-423d-88c3-810b86290da3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_091
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_091 j) = true ∧ (witnessD8_091 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
