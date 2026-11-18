-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_026
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:02.0782+00:00
-- url     : https://prove2.me/submissions/8d081a25-0631-45e2-98bd-ef10fc5e6ae9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_026
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_026 j) = true ∧ (witnessD8_026 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
