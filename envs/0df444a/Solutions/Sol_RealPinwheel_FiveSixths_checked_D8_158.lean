-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_158
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:18:47.591246+00:00
-- url     : https://prove2.me/submissions/149f7b05-0767-40d1-a663-28219843e953

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_158
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_158 j) = true ∧ (witnessD8_158 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
