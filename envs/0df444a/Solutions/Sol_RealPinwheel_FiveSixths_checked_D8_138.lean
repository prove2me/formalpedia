-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_138
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:23.588487+00:00
-- url     : https://prove2.me/submissions/dfae370a-a525-49c0-bdc4-5c8f123bf8c9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_138
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_138 j) = true ∧ (witnessD8_138 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
