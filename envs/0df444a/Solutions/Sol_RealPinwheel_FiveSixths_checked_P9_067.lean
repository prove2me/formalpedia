-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_067
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:43:56.641544+00:00
-- url     : https://prove2.me/submissions/0c55bdd5-dca1-41a7-855f-d3b12f3e2db3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_067
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_067 j) = true ∧ (witnessP9_067 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
