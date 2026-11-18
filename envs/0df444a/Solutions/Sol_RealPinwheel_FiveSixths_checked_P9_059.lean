-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_059
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:49.086211+00:00
-- url     : https://prove2.me/submissions/7343ac1e-8889-4972-9b5f-89c5eefd6e81

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_059
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_059 j) = true ∧ (witnessP9_059 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
