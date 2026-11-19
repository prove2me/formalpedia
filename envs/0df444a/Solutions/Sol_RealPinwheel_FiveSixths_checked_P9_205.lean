-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_205
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:40:46.78419+00:00
-- url     : https://prove2.me/submissions/1b9474f2-96e9-4012-a559-17d34a44e4da

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_205
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessP9_205 j) = true ∧ (witnessP9_205 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
