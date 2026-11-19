-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_146
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:12:31.907171+00:00
-- url     : https://prove2.me/submissions/9dbdfda9-7c21-4a9b-8117-fc0aee68173c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_146
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_146 j) = true ∧ (witnessD8_146 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
