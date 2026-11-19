-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_005
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:52:42.391775+00:00
-- url     : https://prove2.me/submissions/92a1c33c-519c-4216-bdf5-08211853dd72

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_005
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessP9_005 j) = true ∧ (witnessP9_005 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
