-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_317
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:43:18.060715+00:00
-- url     : https://prove2.me/submissions/e47f6132-f11c-4362-8a86-b946f677a1a3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_317
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 65, witnessCheck (witnessP9_317 j) = true ∧ (witnessP9_317 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
