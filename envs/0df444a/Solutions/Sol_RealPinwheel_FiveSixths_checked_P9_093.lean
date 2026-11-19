-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_093
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:26:10.218595+00:00
-- url     : https://prove2.me/submissions/ddaca9d3-fd97-44c2-940e-56decd7f8f19

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_093
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_093 j) = true ∧ (witnessP9_093 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
