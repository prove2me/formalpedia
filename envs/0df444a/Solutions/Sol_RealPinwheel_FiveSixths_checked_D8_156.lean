-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_156
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:18:46.481206+00:00
-- url     : https://prove2.me/submissions/8aced505-5010-42e5-bf5b-c95a634fd6df

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_156
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_156 j) = true ∧ (witnessD8_156 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
