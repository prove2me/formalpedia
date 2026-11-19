-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_193
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:14:56.89049+00:00
-- url     : https://prove2.me/submissions/e220adc5-8838-4977-9733-415c5ac81afa

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_193
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessP9_193 j) = true ∧ (witnessP9_193 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
