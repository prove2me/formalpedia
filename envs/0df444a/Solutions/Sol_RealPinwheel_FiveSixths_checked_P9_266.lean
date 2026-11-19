-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_266
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:14:34.876122+00:00
-- url     : https://prove2.me/submissions/3e48ccdf-0277-495f-90c3-be50a796d3ab

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_266
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 37, witnessCheck (witnessP9_266 j) = true ∧ (witnessP9_266 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
