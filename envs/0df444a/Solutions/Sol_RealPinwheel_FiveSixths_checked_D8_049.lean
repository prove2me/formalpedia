-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_049
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:57.427553+00:00
-- url     : https://prove2.me/submissions/b2a8ae5c-7402-441c-b5f3-b02ffdacd179

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_049
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_049 j) = true ∧ (witnessD8_049 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
