-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_059
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:30.873204+00:00
-- url     : https://prove2.me/submissions/296785d7-7b5e-402d-84ba-685f05019cc6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_059
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_059 j) = true ∧ (witnessD8_059 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
