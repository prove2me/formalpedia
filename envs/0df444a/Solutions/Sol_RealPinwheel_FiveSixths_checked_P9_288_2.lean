-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_288
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:35:18.461062+00:00
-- url     : https://prove2.me/submissions/09366e9c-69a0-4c51-86b7-237a4cfa9ad4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_288
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 44, witnessCheck (witnessP9_288 j) = true ∧ (witnessP9_288 j).length ≤ 1800 := by
  decide +kernel
