-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_258
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:07:57.836745+00:00
-- url     : https://prove2.me/submissions/d1a3770c-1bf0-42f8-ac00-74f0912d4137

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_258
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 34, witnessCheck (witnessP9_258 j) = true ∧ (witnessP9_258 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
