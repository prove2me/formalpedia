-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_297
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:21.413363+00:00
-- url     : https://prove2.me/submissions/bfe3dafe-3f54-4c20-93b6-1e86606659ef

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_297
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 50, witnessCheck (witnessP9_297 j) = true ∧ (witnessP9_297 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
