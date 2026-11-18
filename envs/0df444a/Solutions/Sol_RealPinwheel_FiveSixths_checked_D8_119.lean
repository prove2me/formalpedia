-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_119
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:45:56.259092+00:00
-- url     : https://prove2.me/submissions/71ca11aa-62b8-4adf-a8b2-b5a083b56097

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_119
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_119 j) = true ∧ (witnessD8_119 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
