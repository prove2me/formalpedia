-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_176
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:01:07.425999+00:00
-- url     : https://prove2.me/submissions/af18a253-63bc-4e20-b7a4-6b1933e330d5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_176
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_176 j) = true ∧ (witnessP9_176 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
