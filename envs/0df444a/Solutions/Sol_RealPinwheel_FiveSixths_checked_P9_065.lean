-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_065
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:42:27.419223+00:00
-- url     : https://prove2.me/submissions/2ac81819-6500-4a93-b3b1-bab1e6c8981a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_065
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_065 j) = true ∧ (witnessP9_065 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
