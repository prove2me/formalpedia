-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_210
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:35:01.128925+00:00
-- url     : https://prove2.me/submissions/3fea72fa-8504-42b7-a301-c843f67d7af6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_210
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_210 j) = true ∧ (witnessP9_210 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
