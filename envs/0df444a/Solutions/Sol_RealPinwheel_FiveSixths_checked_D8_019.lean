-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_019
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:25.649951+00:00
-- url     : https://prove2.me/submissions/2bcc4eb4-899a-4b42-a436-cc7038d6bc1d

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_019
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_019 j) = true ∧ (witnessD8_019 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
