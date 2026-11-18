-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:19:56.288075+00:00
-- url     : https://prove2.me/submissions/ae0f73d9-a787-403d-a45a-4f690d045558

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_001
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessD8_001 j) = true ∧ (witnessD8_001 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
