-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_283
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:21:41.21393+00:00
-- url     : https://prove2.me/submissions/bd576c37-1241-4bdb-b38e-73fb72a7e5a1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_283
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 42, witnessCheck (witnessP9_283 j) = true ∧ (witnessP9_283 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
