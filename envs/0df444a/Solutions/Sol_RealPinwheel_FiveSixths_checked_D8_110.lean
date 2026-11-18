-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_110
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:08.313805+00:00
-- url     : https://prove2.me/submissions/57226616-e384-4bf6-aac5-771f79a5e606

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_110
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_110 j) = true ∧ (witnessD8_110 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
