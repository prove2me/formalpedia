-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_251
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:05:18.276228+00:00
-- url     : https://prove2.me/submissions/81f8bdb3-7c71-4d82-9a08-6ac7d8e9448e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_251
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 33, witnessCheck (witnessP9_251 j) = true ∧ (witnessP9_251 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
