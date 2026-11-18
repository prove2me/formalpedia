-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_049
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:20:59.118347+00:00
-- url     : https://prove2.me/submissions/cfc94890-b8d3-4e01-afcd-bca26b278877

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_049
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_049 j) = true ∧ (witnessP9_049 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
