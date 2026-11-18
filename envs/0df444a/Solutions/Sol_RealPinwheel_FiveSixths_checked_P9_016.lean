-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_016
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:56.372754+00:00
-- url     : https://prove2.me/submissions/e929fbb5-9ab2-448c-9b19-86936dfca89a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_016
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_016 j) = true ∧ (witnessP9_016 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
