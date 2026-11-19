-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_087
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:20:01.649843+00:00
-- url     : https://prove2.me/submissions/c6d1d053-7e4c-4bb1-afcf-36f080ab7983

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_087
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_087 j) = true ∧ (witnessP9_087 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
