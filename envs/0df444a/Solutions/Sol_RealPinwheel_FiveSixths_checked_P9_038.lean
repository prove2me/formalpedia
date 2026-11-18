-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_038
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:06:44.950099+00:00
-- url     : https://prove2.me/submissions/5efbd082-68f7-4e7a-84f2-203283d4212a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_038
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_038 j) = true ∧ (witnessP9_038 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
