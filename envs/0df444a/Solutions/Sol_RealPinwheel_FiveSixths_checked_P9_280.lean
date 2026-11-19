-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_280
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:18:03.630893+00:00
-- url     : https://prove2.me/submissions/3f21dd3e-8f66-49fa-9855-9c53b6fcc742

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_280
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_280 j) = true ∧ (witnessP9_280 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
