-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_072
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:00:38.525792+00:00
-- url     : https://prove2.me/submissions/be6832e5-e568-4187-b7b3-8d4f0c79af96

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_072
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 7, witnessCheck (witnessP9_072 j) = true ∧ (witnessP9_072 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
