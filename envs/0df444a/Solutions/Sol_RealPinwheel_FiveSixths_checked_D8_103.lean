-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_103
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:32:55.807416+00:00
-- url     : https://prove2.me/submissions/64b684d8-1647-49a0-b85e-6cfce006af0a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_103
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD8_103 j) = true ∧ (witnessD8_103 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
