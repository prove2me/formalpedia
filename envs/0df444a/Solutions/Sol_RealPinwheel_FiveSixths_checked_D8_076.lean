-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_076
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:59.748339+00:00
-- url     : https://prove2.me/submissions/cd5561ad-8db3-49db-a977-46c06d11be0d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_076
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_076 j) = true ∧ (witnessD8_076 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
