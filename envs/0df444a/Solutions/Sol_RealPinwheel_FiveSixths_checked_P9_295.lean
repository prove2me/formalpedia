-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_295
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:31:53.455186+00:00
-- url     : https://prove2.me/submissions/2e2e8369-1320-4986-96d9-d0b682a4a98b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_295
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 47, witnessCheck (witnessP9_295 j) = true ∧ (witnessP9_295 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
