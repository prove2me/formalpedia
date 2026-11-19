-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_303
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:36:52.565245+00:00
-- url     : https://prove2.me/submissions/cb15bc41-2d1c-43b9-a59a-de4a0a242c50

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_303
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 52, witnessCheck (witnessP9_303 j) = true ∧ (witnessP9_303 j).length ≤ 1800 := by
  decide +kernel
