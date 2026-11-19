-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_104
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:44:23.742194+00:00
-- url     : https://prove2.me/submissions/8e54bd16-4efd-4e43-8bfe-225f7d218e02

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_104
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_104 j) = true ∧ (witnessP9_104 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
