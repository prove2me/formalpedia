-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_155
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:16:16.656961+00:00
-- url     : https://prove2.me/submissions/1a72733f-e93d-450f-ba38-2d22ea975683

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_155
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_155 j) = true ∧ (witnessD8_155 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
