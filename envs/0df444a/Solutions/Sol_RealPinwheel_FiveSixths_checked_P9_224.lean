-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_224
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:57:47.47185+00:00
-- url     : https://prove2.me/submissions/b959cd7c-a684-489d-9ef8-c62c3f65202f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_224
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessP9_224 j) = true ∧ (witnessP9_224 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
