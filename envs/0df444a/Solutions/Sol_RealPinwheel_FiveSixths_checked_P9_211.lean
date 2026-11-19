-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_211
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:26.660273+00:00
-- url     : https://prove2.me/submissions/16d3d8fa-b381-4122-af15-829dc409ba51

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_211
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_211 j) = true ∧ (witnessP9_211 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
