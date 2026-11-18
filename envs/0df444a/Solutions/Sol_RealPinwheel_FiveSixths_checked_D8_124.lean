-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_124
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:53:33.93762+00:00
-- url     : https://prove2.me/submissions/c14b4c09-0099-4dee-918a-19c4e2d23e37

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_124
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD8_124 j) = true ∧ (witnessD8_124 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
