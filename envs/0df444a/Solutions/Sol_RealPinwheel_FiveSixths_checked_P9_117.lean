-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_117
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:54:40.432479+00:00
-- url     : https://prove2.me/submissions/64ae0826-cf84-4a6e-b865-e3783c15e34e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_117
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_117 j) = true ∧ (witnessP9_117 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
