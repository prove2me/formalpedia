-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_169
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:48.225627+00:00
-- url     : https://prove2.me/submissions/cdff4d51-b5a6-4f29-a16d-83a1ae8982d7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_169
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_169 j) = true ∧ (witnessP9_169 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
