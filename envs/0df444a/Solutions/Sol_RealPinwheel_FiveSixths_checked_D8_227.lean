-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_227
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:14:48.601961+00:00
-- url     : https://prove2.me/submissions/ab3a00b4-ecc0-4313-a61b-8881fcad85fd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_227
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD8_227 j) = true ∧ (witnessD8_227 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
