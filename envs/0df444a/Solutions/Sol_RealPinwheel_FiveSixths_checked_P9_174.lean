-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_174
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:09:12.533544+00:00
-- url     : https://prove2.me/submissions/67e0fe5d-ce52-4cde-897d-937e0342ad2f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_174
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessP9_174 j) = true ∧ (witnessP9_174 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
