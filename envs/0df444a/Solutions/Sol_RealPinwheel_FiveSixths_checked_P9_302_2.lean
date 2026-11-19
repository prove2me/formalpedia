-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_P9_302
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:38:24.314473+00:00
-- url     : https://prove2.me/submissions/f450689d-0c47-40ad-bdcc-7b5bd315149b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_302
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 51, witnessCheck (witnessP9_302 j) = true ∧ (witnessP9_302 j).length ≤ 1800 := by
  decide +kernel
