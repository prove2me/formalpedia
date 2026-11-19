-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_264
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:12:34.554361+00:00
-- url     : https://prove2.me/submissions/37b71f7d-be6a-440a-96d1-464719387cca

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_264
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 36, witnessCheck (witnessP9_264 j) = true ∧ (witnessP9_264 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
