-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_134
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:58:14.803902+00:00
-- url     : https://prove2.me/submissions/baae924b-b2ba-4264-b9ce-868b7af8fd0b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_134
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_134 j) = true ∧ (witnessD8_134 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
