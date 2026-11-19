-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_173
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:29:42.603037+00:00
-- url     : https://prove2.me/submissions/0d40a596-1886-4004-acab-cc6461d18c46

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_173
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD8_173 j) = true ∧ (witnessD8_173 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
