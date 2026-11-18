-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_095
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:24:09.182757+00:00
-- url     : https://prove2.me/submissions/e2b4f8ed-db1f-4de2-b91c-f594f37078b6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_095
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_095 j) = true ∧ (witnessD8_095 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
