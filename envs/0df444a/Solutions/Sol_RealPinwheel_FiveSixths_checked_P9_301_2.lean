-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_301
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:40:08.484917+00:00
-- url     : https://prove2.me/submissions/5bd55fe5-9d2a-4e96-9465-6c2325b00e95

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_301
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 51, witnessCheck (witnessP9_301 j) = true ∧ (witnessP9_301 j).length ≤ 1800 := by
  decide +kernel
