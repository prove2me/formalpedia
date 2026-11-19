-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_327
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:51:21.226453+00:00
-- url     : https://prove2.me/submissions/f3f3e2ca-366c-4551-a2db-9cdc47c915da

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_327
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 83, witnessCheck (witnessP9_327 j) = true ∧ (witnessP9_327 j).length ≤ 1800 := by
  decide +kernel
