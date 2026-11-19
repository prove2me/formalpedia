-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_299
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:32:59.93101+00:00
-- url     : https://prove2.me/submissions/9fe318c4-d7d1-4189-9b42-f4f8f3b8ae63

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_299
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 50, witnessCheck (witnessP9_299 j) = true ∧ (witnessP9_299 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
