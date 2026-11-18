-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_018
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:20.530076+00:00
-- url     : https://prove2.me/submissions/edd828ea-534c-4346-ae33-2a61f12d82ba

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_018
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD7_018 j) = true ∧ (witnessD7_018 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
