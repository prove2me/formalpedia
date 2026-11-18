-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_104
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:29.016986+00:00
-- url     : https://prove2.me/submissions/43f489f2-ea54-4c02-89f3-8f6d32ba5d13

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_104
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_104 j) = true ∧ (witnessD8_104 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
