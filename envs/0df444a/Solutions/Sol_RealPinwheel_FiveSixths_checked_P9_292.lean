-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_292
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:26:40.010783+00:00
-- url     : https://prove2.me/submissions/d46d0022-aa5f-463a-84d7-de2f1ccce0dc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_292
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_292 j) = true ∧ (witnessP9_292 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
