-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_246
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:57:47.124266+00:00
-- url     : https://prove2.me/submissions/4651bbb8-fc87-4f53-8517-126149a2388a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_246
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_246 j) = true ∧ (witnessP9_246 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
