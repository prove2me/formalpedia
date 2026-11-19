-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_325
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:48:02.0633+00:00
-- url     : https://prove2.me/submissions/bb6be4c2-83cf-48dd-a64a-03e43a390dc7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_325
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 77, witnessCheck (witnessP9_325 j) = true ∧ (witnessP9_325 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
