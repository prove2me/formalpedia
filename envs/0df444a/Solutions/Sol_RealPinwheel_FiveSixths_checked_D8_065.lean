-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_065
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:40.055319+00:00
-- url     : https://prove2.me/submissions/20510ad3-274d-401e-8d6c-cea9503bbaa2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_065
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_065 j) = true ∧ (witnessD8_065 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
