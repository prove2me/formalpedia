-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_011
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:25.244519+00:00
-- url     : https://prove2.me/submissions/88c03f0b-bbad-43e0-81a3-0dd8337c33b9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_011
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_011 j) = true ∧ (witnessP9_011 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
