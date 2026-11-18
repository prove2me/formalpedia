-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_060
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:07.295461+00:00
-- url     : https://prove2.me/submissions/dd5c77a6-2660-4bf6-a367-4565c186c99b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_060
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_060 j) = true ∧ (witnessP9_060 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
