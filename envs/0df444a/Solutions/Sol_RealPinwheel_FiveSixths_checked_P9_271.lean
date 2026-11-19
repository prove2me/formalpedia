-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_271
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:14:56.136014+00:00
-- url     : https://prove2.me/submissions/13b3c8ce-a9ac-458c-881a-05a4534aa48d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_271
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessP9_271 j) = true ∧ (witnessP9_271 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
