-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_145
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:41:23.870037+00:00
-- url     : https://prove2.me/submissions/f655ea63-83fa-45f3-82a1-372d8747befd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_145
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessP9_145 j) = true ∧ (witnessP9_145 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
