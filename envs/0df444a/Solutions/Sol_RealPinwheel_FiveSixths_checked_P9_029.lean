-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_029
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:50.653658+00:00
-- url     : https://prove2.me/submissions/29027eeb-12cb-4d3c-a9bb-cd488a839846

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_029
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessP9_029 j) = true ∧ (witnessP9_029 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
