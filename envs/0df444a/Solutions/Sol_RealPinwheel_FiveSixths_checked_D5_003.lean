-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D5_003
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:05:56.77553+00:00
-- url     : https://prove2.me/submissions/8d6f322d-c492-40e0-91e0-67bdd64f1224

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_003
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 69, witnessCheck (witnessD5_003 j) = true ∧ (witnessD5_003 j).length ≤ 32 := by
  intro j
  fin_cases j <;> decide +kernel
