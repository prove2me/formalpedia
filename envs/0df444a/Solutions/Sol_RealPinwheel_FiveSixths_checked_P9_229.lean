-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_229
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:28.337063+00:00
-- url     : https://prove2.me/submissions/4d5ffbe8-7519-4041-a576-8169764e45ce

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_229
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 27, witnessCheck (witnessP9_229 j) = true ∧ (witnessP9_229 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
