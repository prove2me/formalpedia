-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_207
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:54:34.276533+00:00
-- url     : https://prove2.me/submissions/7a78acc1-c05c-4986-aaa8-ccc3ea4035b2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_207
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD8_207 j) = true ∧ (witnessD8_207 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
