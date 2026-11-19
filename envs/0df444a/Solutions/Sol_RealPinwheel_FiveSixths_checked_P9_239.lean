-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_239
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:02:24.086899+00:00
-- url     : https://prove2.me/submissions/c87c4341-25fa-4cf2-8da4-6b32bd41820f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_239
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessP9_239 j) = true ∧ (witnessP9_239 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
