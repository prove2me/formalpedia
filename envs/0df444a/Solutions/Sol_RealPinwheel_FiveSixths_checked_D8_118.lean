-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_118
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:45:00.969861+00:00
-- url     : https://prove2.me/submissions/0b06cb8d-3909-42a6-a1e8-b6c940c486f1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_118
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_118 j) = true ∧ (witnessD8_118 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
