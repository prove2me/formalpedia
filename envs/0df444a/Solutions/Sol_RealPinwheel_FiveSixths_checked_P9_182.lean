-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_182
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:08:33.9832+00:00
-- url     : https://prove2.me/submissions/b61849a3-606b-4ae3-a4ef-ce2bb1798cfa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_182
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_182 j) = true ∧ (witnessP9_182 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
