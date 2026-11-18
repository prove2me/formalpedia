-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_014
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:26.967295+00:00
-- url     : https://prove2.me/submissions/97f0954c-453b-4177-b21e-acaaca62e24c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_014
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessD7_014 j) = true ∧ (witnessD7_014 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
