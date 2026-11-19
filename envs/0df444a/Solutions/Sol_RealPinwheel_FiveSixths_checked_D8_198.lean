-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_198
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:45:58.094169+00:00
-- url     : https://prove2.me/submissions/57e4fb84-1a86-49a0-b0c7-7e97f7261e5e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_198
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_198 j) = true ∧ (witnessD8_198 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
