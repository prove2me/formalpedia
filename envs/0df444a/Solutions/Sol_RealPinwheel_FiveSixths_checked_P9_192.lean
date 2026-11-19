-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_192
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:19:14.304969+00:00
-- url     : https://prove2.me/submissions/583686c9-a942-4f88-bb9d-55912773e591

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_192
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_192 j) = true ∧ (witnessP9_192 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
