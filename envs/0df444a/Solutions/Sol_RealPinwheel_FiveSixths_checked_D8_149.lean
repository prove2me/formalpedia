-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_149
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:11:43.149498+00:00
-- url     : https://prove2.me/submissions/0ac35129-6b3a-4459-ab65-a44c8c72d935

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_149
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_149 j) = true ∧ (witnessD8_149 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
