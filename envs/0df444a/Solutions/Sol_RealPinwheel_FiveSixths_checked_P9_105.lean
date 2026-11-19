-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_105
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:41:24.832768+00:00
-- url     : https://prove2.me/submissions/814049e7-0f7a-4554-90be-992b6fa4260e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_105
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessP9_105 j) = true ∧ (witnessP9_105 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
