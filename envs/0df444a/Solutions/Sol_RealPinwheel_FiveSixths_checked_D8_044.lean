-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_044
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:57:45.359089+00:00
-- url     : https://prove2.me/submissions/10060cfa-c4ff-40d7-b855-49f9e67893d1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_044
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_044 j) = true ∧ (witnessD8_044 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
