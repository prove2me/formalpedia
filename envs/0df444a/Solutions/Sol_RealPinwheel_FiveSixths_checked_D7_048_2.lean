-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_D7_048
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:57:43.813205+00:00
-- url     : https://prove2.me/submissions/b9ae2664-1cdc-4b31-851c-8ee8cfb1c5bb

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_048
open RealPinwheel.FiveSixths

theorem solution : ∀ j : Fin 26, witnessCheck (witnessD7_048 j) = true ∧ (witnessD7_048 j).length ≤ 352 := by
  decide +kernel
