-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_166
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:27:41.32819+00:00
-- url     : https://prove2.me/submissions/d95dce05-39a3-4da7-b50b-0adee28d74a7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_166
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_166 j) = true ∧ (witnessD8_166 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
