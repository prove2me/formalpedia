-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_302
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:34:14.767325+00:00
-- url     : https://prove2.me/submissions/c7a05fe6-1243-488d-afa8-51a174dd3e36

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_302
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 51, witnessCheck (witnessP9_302 j) = true ∧ (witnessP9_302 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
