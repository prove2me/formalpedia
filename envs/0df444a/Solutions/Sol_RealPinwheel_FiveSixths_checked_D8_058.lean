-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_058
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:01:55.012348+00:00
-- url     : https://prove2.me/submissions/51291aa2-aefb-4845-b552-6846226401bd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_058
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_058 j) = true ∧ (witnessD8_058 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
