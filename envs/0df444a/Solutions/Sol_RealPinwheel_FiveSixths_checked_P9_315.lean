-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_315
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:40:41.275203+00:00
-- url     : https://prove2.me/submissions/7f7dfcc7-935d-4fff-b07b-7ae4da2b0281

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_315
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 62, witnessCheck (witnessP9_315 j) = true ∧ (witnessP9_315 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
