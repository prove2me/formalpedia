-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_127
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:11:32.7992+00:00
-- url     : https://prove2.me/submissions/1f376bd4-6357-469c-9347-9d393df8838e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_127
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_127 j) = true ∧ (witnessP9_127 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
