-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_264
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:19:15.55368+00:00
-- url     : https://prove2.me/submissions/2067d0cf-e2c3-4834-9b14-1b1b0111e33c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_264
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 36, witnessCheck (witnessP9_264 j) = true ∧ (witnessP9_264 j).length ≤ 1800 := by
  decide +kernel
