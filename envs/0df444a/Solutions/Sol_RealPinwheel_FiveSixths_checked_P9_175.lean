-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_175
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:11:43.5037+00:00
-- url     : https://prove2.me/submissions/a1512ced-1b73-4398-bf07-e28c9d6bae61

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_175
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessP9_175 j) = true ∧ (witnessP9_175 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
