-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_154
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:16:17.552615+00:00
-- url     : https://prove2.me/submissions/35a9335b-38d6-4cde-b41b-aa28647b8b31

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_154
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_154 j) = true ∧ (witnessD8_154 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
