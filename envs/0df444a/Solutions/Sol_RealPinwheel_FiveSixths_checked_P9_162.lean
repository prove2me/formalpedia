-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_162
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:43.609722+00:00
-- url     : https://prove2.me/submissions/8548ab61-23e5-4d78-9a46-2fcb55337827

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_162
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_162 j) = true ∧ (witnessP9_162 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
