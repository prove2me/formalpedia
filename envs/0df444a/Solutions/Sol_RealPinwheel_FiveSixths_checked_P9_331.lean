-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_331
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:52:53.713957+00:00
-- url     : https://prove2.me/submissions/cf514b9c-e639-4810-9f1b-37d3c9d44a36

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_331
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 93, witnessCheck (witnessP9_331 j) = true ∧ (witnessP9_331 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
