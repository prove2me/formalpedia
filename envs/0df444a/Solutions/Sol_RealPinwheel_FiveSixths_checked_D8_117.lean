-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_117
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:42:14.841134+00:00
-- url     : https://prove2.me/submissions/a5abfe76-5caa-4636-a98e-6854955f67b7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_117
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD8_117 j) = true ∧ (witnessD8_117 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
