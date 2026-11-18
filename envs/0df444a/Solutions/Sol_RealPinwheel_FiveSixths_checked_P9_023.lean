-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_023
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:54:33.881583+00:00
-- url     : https://prove2.me/submissions/e23e7a80-fae9-4275-b98d-4e029969cae7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_023
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_023 j) = true ∧ (witnessP9_023 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
