-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_248
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:38:22.030392+00:00
-- url     : https://prove2.me/submissions/47800785-5ed6-407e-bce5-d76e7289d869

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_248
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessD8_248 j) = true ∧ (witnessD8_248 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
