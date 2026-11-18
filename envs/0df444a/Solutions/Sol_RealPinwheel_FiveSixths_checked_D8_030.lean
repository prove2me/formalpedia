-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_030
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:07.046571+00:00
-- url     : https://prove2.me/submissions/22a7eff0-2b57-4c80-8b2a-7cf13f0800f1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_030
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_030 j) = true ∧ (witnessD8_030 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
