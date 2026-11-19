-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_186
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:40:47.90422+00:00
-- url     : https://prove2.me/submissions/4a065aba-afa1-457a-b66e-a2370b75821e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_186
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_186 j) = true ∧ (witnessD8_186 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
