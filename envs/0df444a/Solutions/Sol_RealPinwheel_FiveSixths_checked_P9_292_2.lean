-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_292
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:30:43.700736+00:00
-- url     : https://prove2.me/submissions/df946f6a-edd7-463d-8d2c-4d485488cbd3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_292
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_292 j) = true ∧ (witnessP9_292 j).length ≤ 1800 := by
  decide +kernel
