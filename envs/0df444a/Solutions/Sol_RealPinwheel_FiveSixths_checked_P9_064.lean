-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_064
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:51.862386+00:00
-- url     : https://prove2.me/submissions/31c62f03-345b-44e2-8638-aa9c986e3946

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_064
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_064 j) = true ∧ (witnessP9_064 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
