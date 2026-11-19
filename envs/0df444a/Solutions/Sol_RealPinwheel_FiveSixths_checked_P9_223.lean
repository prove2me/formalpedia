-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_223
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:39.536195+00:00
-- url     : https://prove2.me/submissions/bf292cce-7f1e-4b31-83ad-e9dbaf677443

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_223
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 26, witnessCheck (witnessP9_223 j) = true ∧ (witnessP9_223 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
