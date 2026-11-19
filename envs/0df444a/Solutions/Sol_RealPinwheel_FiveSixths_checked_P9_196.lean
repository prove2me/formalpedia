-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_196
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:31:16.5121+00:00
-- url     : https://prove2.me/submissions/69e7c911-1ebf-46a6-b9d6-8b667a8924a8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_196
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_196 j) = true ∧ (witnessP9_196 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
