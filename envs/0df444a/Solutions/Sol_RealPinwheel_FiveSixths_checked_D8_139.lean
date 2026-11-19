-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_139
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:02:18.317727+00:00
-- url     : https://prove2.me/submissions/1e4d3e47-69e1-40e3-8681-276a683db637

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_139
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_139 j) = true ∧ (witnessD8_139 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
