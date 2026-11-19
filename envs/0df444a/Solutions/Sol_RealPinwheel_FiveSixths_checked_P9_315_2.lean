-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_315
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:43:19.872203+00:00
-- url     : https://prove2.me/submissions/ee8d9aa6-638f-403b-b303-83d0c30c42a5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_315
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 62, witnessCheck (witnessP9_315 j) = true ∧ (witnessP9_315 j).length ≤ 1800 := by
  decide +kernel
