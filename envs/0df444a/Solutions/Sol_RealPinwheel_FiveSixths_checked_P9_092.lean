-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_092
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:23:52.381702+00:00
-- url     : https://prove2.me/submissions/24093a58-9e51-4d95-96e8-7403435a85f9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_092
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_092 j) = true ∧ (witnessP9_092 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
