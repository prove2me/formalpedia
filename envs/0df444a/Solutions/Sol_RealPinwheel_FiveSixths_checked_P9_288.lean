-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_288
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:25:21.101674+00:00
-- url     : https://prove2.me/submissions/b236c2ca-fe14-481a-b375-d8e33ba1912c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_288
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 44, witnessCheck (witnessP9_288 j) = true ∧ (witnessP9_288 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
