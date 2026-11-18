-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_036
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:03:28.338317+00:00
-- url     : https://prove2.me/submissions/db6ca5fc-7fac-43b2-bd2c-37b9e632735f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_036
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessP9_036 j) = true ∧ (witnessP9_036 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
