-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_025
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:55.267627+00:00
-- url     : https://prove2.me/submissions/63bcd987-1ccc-4d41-9e97-1e6623fbe4f4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_025
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessP9_025 j) = true ∧ (witnessP9_025 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
