-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_087
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:25:20.032524+00:00
-- url     : https://prove2.me/submissions/cf0a5751-1c68-4538-8fca-259fe6d4180b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_087
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 10, witnessCheck (witnessD8_087 j) = true ∧ (witnessD8_087 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
