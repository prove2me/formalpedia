-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_008
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:29:58.716621+00:00
-- url     : https://prove2.me/submissions/371af200-8388-4fbc-bee7-14ffad50a6be

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_008
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessD6_008 j) = true ∧ (witnessD6_008 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
