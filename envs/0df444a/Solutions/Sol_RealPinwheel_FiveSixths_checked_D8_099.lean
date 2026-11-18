-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_099
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:26:30.145275+00:00
-- url     : https://prove2.me/submissions/e9e43062-66d2-4232-92c4-053a6d577c9e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_099
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_099 j) = true ∧ (witnessD8_099 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
