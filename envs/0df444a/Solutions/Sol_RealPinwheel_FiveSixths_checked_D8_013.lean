-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_013
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:56.807613+00:00
-- url     : https://prove2.me/submissions/8b8026f7-20b1-4062-a199-97923b7604e5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_013
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD8_013 j) = true ∧ (witnessD8_013 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
