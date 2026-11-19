-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_180
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:33:40.57885+00:00
-- url     : https://prove2.me/submissions/f3d57e08-8544-482e-99e9-dd2da91e3035

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_180
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_180 j) = true ∧ (witnessD8_180 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
