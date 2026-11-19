-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_291
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:32:18.327627+00:00
-- url     : https://prove2.me/submissions/f1a19fb2-362d-4032-b849-f289b0811c9e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_291
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 46, witnessCheck (witnessP9_291 j) = true ∧ (witnessP9_291 j).length ≤ 1800 := by
  decide +kernel
