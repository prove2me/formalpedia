-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_044
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:53:00.146735+00:00
-- url     : https://prove2.me/submissions/3b78cc75-54f1-45a9-887e-0ef630791c07

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_044
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessD7_044 j) = true ∧ (witnessD7_044 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
