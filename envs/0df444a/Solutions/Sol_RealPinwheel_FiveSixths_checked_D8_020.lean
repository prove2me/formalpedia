-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_020
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:17.255671+00:00
-- url     : https://prove2.me/submissions/ef8d9841-0a48-4e2d-abf8-b07787fb1289

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_020
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_020 j) = true ∧ (witnessD8_020 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
