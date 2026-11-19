-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_123
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:54:22.589197+00:00
-- url     : https://prove2.me/submissions/efd47489-db34-4fc1-af63-8842f48bbf60

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_123
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_123 j) = true ∧ (witnessD8_123 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
