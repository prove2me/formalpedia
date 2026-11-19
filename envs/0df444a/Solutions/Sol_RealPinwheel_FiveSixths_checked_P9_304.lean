-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_304
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:37:48.857214+00:00
-- url     : https://prove2.me/submissions/44b26e8f-42dc-465d-9f15-4f56275dfec6

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_304
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 53, witnessCheck (witnessP9_304 j) = true ∧ (witnessP9_304 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
