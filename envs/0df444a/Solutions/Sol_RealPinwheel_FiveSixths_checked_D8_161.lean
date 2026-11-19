-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_161
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:21:31.4072+00:00
-- url     : https://prove2.me/submissions/cb19e353-ac66-4cff-b9b3-6816ad5815a1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_161
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_161 j) = true ∧ (witnessD8_161 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
