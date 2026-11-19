-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_135
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:25:21.416775+00:00
-- url     : https://prove2.me/submissions/2a323d7d-4b7d-41cc-8436-04b8a3b9e245

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_135
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_135 j) = true ∧ (witnessP9_135 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
