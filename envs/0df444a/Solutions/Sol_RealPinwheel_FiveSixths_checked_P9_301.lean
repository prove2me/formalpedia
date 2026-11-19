-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_301
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:34:15.468199+00:00
-- url     : https://prove2.me/submissions/333ef419-93ae-4186-ac5b-c424e74a1bf2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_301
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 51, witnessCheck (witnessP9_301 j) = true ∧ (witnessP9_301 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
