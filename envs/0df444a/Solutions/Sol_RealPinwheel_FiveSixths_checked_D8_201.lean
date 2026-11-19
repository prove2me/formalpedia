-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_201
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:49:40.427891+00:00
-- url     : https://prove2.me/submissions/c6462f49-0542-4c4c-acc4-002356ae933a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_201
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD8_201 j) = true ∧ (witnessD8_201 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
