-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_318
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:44:55.36969+00:00
-- url     : https://prove2.me/submissions/24096709-38e7-4071-a363-bcc2b2236e6f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_318
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 67, witnessCheck (witnessP9_318 j) = true ∧ (witnessP9_318 j).length ≤ 1800 := by
  decide +kernel
