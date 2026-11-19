-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_310
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:39:03.414695+00:00
-- url     : https://prove2.me/submissions/622c3c0e-81c6-45e0-977e-2eda4e7a16fe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_310
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 57, witnessCheck (witnessP9_310 j) = true ∧ (witnessP9_310 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
