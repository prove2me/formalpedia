-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_091
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:25:16.256451+00:00
-- url     : https://prove2.me/submissions/3c0f5fe1-72be-4c54-b67b-b8e3925c49fd

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_091
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_091 j) = true ∧ (witnessP9_091 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
