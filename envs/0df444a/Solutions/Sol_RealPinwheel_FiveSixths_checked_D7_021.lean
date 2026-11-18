-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_021
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:39:34.065336+00:00
-- url     : https://prove2.me/submissions/28618c53-ed84-4eb5-94ea-2386e2fd9acc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_021
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD7_021 j) = true ∧ (witnessD7_021 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
