-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_004
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:49.678693+00:00
-- url     : https://prove2.me/submissions/49bbc0d0-9a00-4442-b97e-acf802905ed1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_004
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_004 j) = true ∧ (witnessP9_004 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
