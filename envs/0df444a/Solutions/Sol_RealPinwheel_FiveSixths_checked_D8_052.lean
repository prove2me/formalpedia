-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_052
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:56:59.043206+00:00
-- url     : https://prove2.me/submissions/dca08296-c6ba-4d8e-8c8a-9e65f876ed9f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_052
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_052 j) = true ∧ (witnessD8_052 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
