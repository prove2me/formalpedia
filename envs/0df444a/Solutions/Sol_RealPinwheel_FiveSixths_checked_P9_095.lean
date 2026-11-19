-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_095
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:28:07.177384+00:00
-- url     : https://prove2.me/submissions/cfb49d25-3869-4480-9ab7-4f4c292214f8

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_095
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_095 j) = true ∧ (witnessP9_095 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
