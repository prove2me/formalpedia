-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_159
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:22:29.3673+00:00
-- url     : https://prove2.me/submissions/6a39fb60-5c49-4f64-aa77-a5485061233c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_159
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_159 j) = true ∧ (witnessD8_159 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
