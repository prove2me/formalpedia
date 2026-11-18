-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_071
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:12.798194+00:00
-- url     : https://prove2.me/submissions/82f6c500-1a71-45e9-8ae3-77f35ff7cbd7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_071
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_071 j) = true ∧ (witnessD8_071 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
