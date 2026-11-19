-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_148
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:15:20.312844+00:00
-- url     : https://prove2.me/submissions/b2239909-3163-4184-a0d3-4745de98fe97

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_148
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD8_148 j) = true ∧ (witnessD8_148 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
