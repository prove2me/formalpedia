-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_237
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:50:17.980327+00:00
-- url     : https://prove2.me/submissions/a7595f8b-bcaa-4570-8780-bb31ce09adc7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_237
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessP9_237 j) = true ∧ (witnessP9_237 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
