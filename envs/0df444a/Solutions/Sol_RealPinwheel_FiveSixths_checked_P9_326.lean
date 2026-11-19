-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_326
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:47:59.774513+00:00
-- url     : https://prove2.me/submissions/8288e30c-6ce1-46a9-803a-ad8f76f0fdb5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_326
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 79, witnessCheck (witnessP9_326 j) = true ∧ (witnessP9_326 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
