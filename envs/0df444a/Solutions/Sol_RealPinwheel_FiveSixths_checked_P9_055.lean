-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_055
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:33:12.863665+00:00
-- url     : https://prove2.me/submissions/9f064d6e-c405-4e68-8bc3-d7554f349f10

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_055
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_055 j) = true ∧ (witnessP9_055 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
