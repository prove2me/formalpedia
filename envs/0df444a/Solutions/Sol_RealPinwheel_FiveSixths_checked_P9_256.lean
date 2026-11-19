-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_256
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:07:08.562934+00:00
-- url     : https://prove2.me/submissions/bbbdcb3f-4659-4b8f-a8e2-a200963e90d8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_256
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessP9_256 j) = true ∧ (witnessP9_256 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
