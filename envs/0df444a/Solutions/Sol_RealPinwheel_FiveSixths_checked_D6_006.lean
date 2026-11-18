-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_006
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:53:25.7252+00:00
-- url     : https://prove2.me/submissions/d433a1ac-7020-40d6-89a5-eeacfeb60d50

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_006
open RealPinwheel.FiveSixths
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD6_006 j) = true ∧ (witnessD6_006 j).length ≤ 64 := by
  decide +kernel
