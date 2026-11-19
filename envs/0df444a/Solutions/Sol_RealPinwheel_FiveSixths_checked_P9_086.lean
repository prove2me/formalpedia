-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_086
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:32.315194+00:00
-- url     : https://prove2.me/submissions/3d885757-208b-490c-9693-2af1c93820b5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_086
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessP9_086 j) = true ∧ (witnessP9_086 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
