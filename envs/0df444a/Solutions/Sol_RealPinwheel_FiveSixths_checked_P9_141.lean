-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_141
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:36:07.211191+00:00
-- url     : https://prove2.me/submissions/78a8f116-fcd6-4209-b03e-b574b528c05b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_141
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessP9_141 j) = true ∧ (witnessP9_141 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
