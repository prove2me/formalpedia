-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_116
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:47.79339+00:00
-- url     : https://prove2.me/submissions/da200feb-480d-4419-a829-1b3286e44692

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_116
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_116 j) = true ∧ (witnessD8_116 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
