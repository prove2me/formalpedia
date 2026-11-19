-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_129
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:56:30.115344+00:00
-- url     : https://prove2.me/submissions/c15aa1ae-2c74-4151-b4c0-23dc304460bc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_129
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_129 j) = true ∧ (witnessD8_129 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
