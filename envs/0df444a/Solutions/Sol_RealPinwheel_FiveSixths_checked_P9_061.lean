-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_061
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:41:22.282116+00:00
-- url     : https://prove2.me/submissions/986b7541-e54c-4a9d-8661-1a216caeeeda

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_061
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_061 j) = true ∧ (witnessP9_061 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
