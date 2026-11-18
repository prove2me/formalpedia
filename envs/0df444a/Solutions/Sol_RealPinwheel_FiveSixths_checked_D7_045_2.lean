-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_D7_045
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:00:18.539208+00:00
-- url     : https://prove2.me/submissions/4382f515-308d-477c-899a-098d45dcb18f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_045
open RealPinwheel.FiveSixths

theorem solution : ∀ j : Fin 25, witnessCheck (witnessD7_045 j) = true ∧ (witnessD7_045 j).length ≤ 352 := by
  decide +kernel
