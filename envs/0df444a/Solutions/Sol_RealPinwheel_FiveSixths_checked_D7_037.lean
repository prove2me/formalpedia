-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_037
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:47:21.83921+00:00
-- url     : https://prove2.me/submissions/a7b7e319-ea5c-4381-9c59-322280695a63

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_037
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessD7_037 j) = true ∧ (witnessD7_037 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
