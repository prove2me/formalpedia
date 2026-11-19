-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_076
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:03:48.424877+00:00
-- url     : https://prove2.me/submissions/650003fb-bf82-4d14-9767-2d41c45500ff

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_076
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_076 j) = true ∧ (witnessP9_076 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
