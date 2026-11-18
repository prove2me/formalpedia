-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_030
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:06.887846+00:00
-- url     : https://prove2.me/submissions/5fd89fc3-9812-464c-bc4e-6a9687a7b3f6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_030
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD7_030 j) = true ∧ (witnessD7_030 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
