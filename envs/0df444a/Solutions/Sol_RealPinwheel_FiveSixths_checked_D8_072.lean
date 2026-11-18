-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_072
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:33.51807+00:00
-- url     : https://prove2.me/submissions/17f419cc-c711-4cb8-b013-62ce55f0a2be

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_072
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_072 j) = true ∧ (witnessD8_072 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
