-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_113
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:39:06.953984+00:00
-- url     : https://prove2.me/submissions/b562be69-8c23-4647-8f21-90fc2b1985d3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_113
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_113 j) = true ∧ (witnessD8_113 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
