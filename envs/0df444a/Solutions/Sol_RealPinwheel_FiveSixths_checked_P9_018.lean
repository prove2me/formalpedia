-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_018
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:17.705196+00:00
-- url     : https://prove2.me/submissions/f75386ea-8143-4c15-8722-2ad13900f9a9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_018
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_018 j) = true ∧ (witnessP9_018 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
