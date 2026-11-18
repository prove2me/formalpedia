-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_034
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:43.101408+00:00
-- url     : https://prove2.me/submissions/1f6d6916-c9a7-46fa-85a5-1b4ff7b6bee3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_034
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_034 j) = true ∧ (witnessP9_034 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
