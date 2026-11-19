-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_131
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:55:32.589087+00:00
-- url     : https://prove2.me/submissions/f4f1d8b5-e8f0-4b27-9566-afebf0918501

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_131
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_131 j) = true ∧ (witnessD8_131 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
