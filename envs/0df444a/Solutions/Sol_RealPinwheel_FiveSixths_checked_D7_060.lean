-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_060
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:42.965099+00:00
-- url     : https://prove2.me/submissions/ba730cf4-2b73-4653-9b1a-92ae4c4652b2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_060
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessD7_060 j) = true ∧ (witnessD7_060 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
