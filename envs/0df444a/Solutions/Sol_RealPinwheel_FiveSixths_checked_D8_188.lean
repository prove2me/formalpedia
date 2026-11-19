-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_188
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:38:13.33863+00:00
-- url     : https://prove2.me/submissions/e55cb658-a987-4d83-9076-f0817ddcfabe

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_188
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD8_188 j) = true ∧ (witnessD8_188 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
