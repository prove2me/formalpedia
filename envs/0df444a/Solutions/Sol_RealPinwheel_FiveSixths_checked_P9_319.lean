-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_319
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:43:28.40407+00:00
-- url     : https://prove2.me/submissions/eefccc63-9abf-4ae5-98ea-a42db382d839

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_319
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 68, witnessCheck (witnessP9_319 j) = true ∧ (witnessP9_319 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
