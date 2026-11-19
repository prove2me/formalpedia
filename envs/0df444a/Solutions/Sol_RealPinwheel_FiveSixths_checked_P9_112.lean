-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_112
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:48:28.23356+00:00
-- url     : https://prove2.me/submissions/00115410-e7a4-4ebd-aad6-ab2e4dd303e6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_112
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_112 j) = true ∧ (witnessP9_112 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
