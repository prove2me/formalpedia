-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_038
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:03.595859+00:00
-- url     : https://prove2.me/submissions/3d5ee0ee-87ae-4b7d-851b-7cf13e39ff35

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_038
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_038 j) = true ∧ (witnessD8_038 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
