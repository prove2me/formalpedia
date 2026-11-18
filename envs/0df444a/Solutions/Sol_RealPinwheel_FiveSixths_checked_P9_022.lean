-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_022
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:50:42.361269+00:00
-- url     : https://prove2.me/submissions/a1e39d47-b998-4d76-9b0c-eb5b2e8716c6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_022
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_022 j) = true ∧ (witnessP9_022 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
