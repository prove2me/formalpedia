-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_334
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:55:03.878525+00:00
-- url     : https://prove2.me/submissions/82fac1a8-eea1-492c-8766-91fe0d39cf76

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_334
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 118, witnessCheck (witnessP9_334 j) = true ∧ (witnessP9_334 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
