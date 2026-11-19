-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_290
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:33:45.799123+00:00
-- url     : https://prove2.me/submissions/fe50cacc-1135-4b00-ab60-47d6dee4a2f5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_290
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 45, witnessCheck (witnessP9_290 j) = true ∧ (witnessP9_290 j).length ≤ 1800 := by
  decide +kernel
