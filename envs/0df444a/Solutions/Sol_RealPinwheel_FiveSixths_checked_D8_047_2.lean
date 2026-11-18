-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_D8_047
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:59:16.619626+00:00
-- url     : https://prove2.me/submissions/2940093c-7c02-4409-81bc-8faaab205a17

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_047
open RealPinwheel.FiveSixths

theorem solution : ∀ j : Fin 7, witnessCheck (witnessD8_047 j) = true ∧ (witnessD8_047 j).length ≤ 608 := by
  decide +kernel
