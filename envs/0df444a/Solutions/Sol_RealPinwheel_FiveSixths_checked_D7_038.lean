-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_038
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:46.494672+00:00
-- url     : https://prove2.me/submissions/c0830397-6c28-49e1-8545-c2bc6897090a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_038
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD7_038 j) = true ∧ (witnessD7_038 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
