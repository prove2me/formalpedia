-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_050
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:22:25.022194+00:00
-- url     : https://prove2.me/submissions/febe6161-d0eb-44a0-9131-fd6bdfcae5b0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_050
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_050 j) = true ∧ (witnessP9_050 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
