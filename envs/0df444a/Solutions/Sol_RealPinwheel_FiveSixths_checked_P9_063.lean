-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_063
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:44.715832+00:00
-- url     : https://prove2.me/submissions/2d3b1cf1-a0e2-4ed6-ba17-2c09a5412170

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_063
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_063 j) = true ∧ (witnessP9_063 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
