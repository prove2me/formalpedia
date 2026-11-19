-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_097
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:29:25.10054+00:00
-- url     : https://prove2.me/submissions/2865b9e8-101e-42c0-aae7-239996d9af19

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_097
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_097 j) = true ∧ (witnessP9_097 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
