-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_069
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:07:36.017405+00:00
-- url     : https://prove2.me/submissions/3d1871a1-19e1-4965-9901-e8c4039629c5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_069
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_069 j) = true ∧ (witnessD8_069 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
