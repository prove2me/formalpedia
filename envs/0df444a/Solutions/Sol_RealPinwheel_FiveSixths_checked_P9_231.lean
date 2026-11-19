-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_231
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:46:16.252447+00:00
-- url     : https://prove2.me/submissions/4907b7d7-989b-4ecf-b708-2f517e008378

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_231
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_231 j) = true ∧ (witnessP9_231 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
