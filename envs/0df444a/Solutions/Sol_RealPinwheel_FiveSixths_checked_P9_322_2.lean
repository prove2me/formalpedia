-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_322
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:46:30.508114+00:00
-- url     : https://prove2.me/submissions/8c613a9d-8011-4efe-9344-03190db35713

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_322
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 72, witnessCheck (witnessP9_322 j) = true ∧ (witnessP9_322 j).length ≤ 1800 := by
  decide +kernel
