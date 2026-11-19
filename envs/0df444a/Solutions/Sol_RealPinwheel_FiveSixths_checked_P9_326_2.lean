-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_326
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:49:45.321281+00:00
-- url     : https://prove2.me/submissions/eed3104d-73fb-40fc-8536-a5ec46b378a2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_326
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 79, witnessCheck (witnessP9_326 j) = true ∧ (witnessP9_326 j).length ≤ 1800 := by
  decide +kernel
