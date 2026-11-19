-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_214
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:42:58.001339+00:00
-- url     : https://prove2.me/submissions/c3aa4850-dfee-46e4-b4f5-42572eb66f55

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_214
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_214 j) = true ∧ (witnessP9_214 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
