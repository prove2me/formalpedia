-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_094
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:24:52.718951+00:00
-- url     : https://prove2.me/submissions/4f06d6e4-0601-409e-a3e4-8fe1492152c3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_094
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_094 j) = true ∧ (witnessP9_094 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
