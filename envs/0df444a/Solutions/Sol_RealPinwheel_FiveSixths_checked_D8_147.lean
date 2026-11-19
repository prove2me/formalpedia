-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_147
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:11:22.753338+00:00
-- url     : https://prove2.me/submissions/2531c91a-66c5-43a6-a05c-ff09f0cb22a0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_147
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_147 j) = true ∧ (witnessD8_147 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
