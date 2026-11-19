-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_181
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:43.639018+00:00
-- url     : https://prove2.me/submissions/827a3078-06d0-4ba7-8943-ec43a4426aed

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_181
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_181 j) = true ∧ (witnessP9_181 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
