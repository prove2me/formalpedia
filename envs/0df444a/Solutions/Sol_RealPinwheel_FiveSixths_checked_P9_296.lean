-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_296
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:30:11.762201+00:00
-- url     : https://prove2.me/submissions/8f91c185-f8ca-4fc8-8e7f-db48a69e7cce

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_296
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 49, witnessCheck (witnessP9_296 j) = true ∧ (witnessP9_296 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
