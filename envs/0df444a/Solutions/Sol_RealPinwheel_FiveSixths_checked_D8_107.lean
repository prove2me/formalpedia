-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_107
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:04.453168+00:00
-- url     : https://prove2.me/submissions/75d46198-24d3-4cd8-b8af-9d2dc8782a9b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_107
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_107 j) = true ∧ (witnessD8_107 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
