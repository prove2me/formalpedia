-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_312
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:41:49.958197+00:00
-- url     : https://prove2.me/submissions/48e93f39-9ea9-4b02-a3e3-af7b900acac1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_312
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 58, witnessCheck (witnessP9_312 j) = true ∧ (witnessP9_312 j).length ≤ 1800 := by
  decide +kernel
