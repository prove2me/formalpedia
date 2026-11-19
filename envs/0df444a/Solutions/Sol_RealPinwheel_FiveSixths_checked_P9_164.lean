-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_164
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:02:29.56247+00:00
-- url     : https://prove2.me/submissions/bf7ec054-6dba-40d5-b4b6-108d8bccd789

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_164
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_164 j) = true ∧ (witnessP9_164 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
