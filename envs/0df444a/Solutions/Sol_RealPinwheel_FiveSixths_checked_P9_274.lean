-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_274
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:15:45.758267+00:00
-- url     : https://prove2.me/submissions/c5982b93-6215-4799-acde-760d9c3dbf4a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_274
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 39, witnessCheck (witnessP9_274 j) = true ∧ (witnessP9_274 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
