-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_202
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:50:33.154079+00:00
-- url     : https://prove2.me/submissions/9ff2a9ab-bfae-4741-8cb4-137c3cbf8134

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_202
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 23, witnessCheck (witnessD8_202 j) = true ∧ (witnessD8_202 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
