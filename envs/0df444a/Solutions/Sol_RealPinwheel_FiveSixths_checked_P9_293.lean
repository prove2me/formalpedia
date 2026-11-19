-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_293
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:26:29.992421+00:00
-- url     : https://prove2.me/submissions/0156951b-e27d-4b9e-a1bb-bb89f07b614a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_293
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_293 j) = true ∧ (witnessP9_293 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
