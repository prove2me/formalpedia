-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_077
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:08:26.262599+00:00
-- url     : https://prove2.me/submissions/6956cd6b-a71f-4434-893b-6cba878f133c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_077
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD8_077 j) = true ∧ (witnessD8_077 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
