-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_009
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:35:40.756199+00:00
-- url     : https://prove2.me/submissions/f668bff7-0795-46a0-b045-895cd9559320

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_009
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessD8_009 j) = true ∧ (witnessD8_009 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
