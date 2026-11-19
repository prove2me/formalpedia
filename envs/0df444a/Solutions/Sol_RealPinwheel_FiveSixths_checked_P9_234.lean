-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_234
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:44:45.002333+00:00
-- url     : https://prove2.me/submissions/0e2e24a6-cd38-41c7-a48f-97b23f1c9420

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_234
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_234 j) = true ∧ (witnessP9_234 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
