-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_115
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:50:17.504464+00:00
-- url     : https://prove2.me/submissions/c161aed2-91d4-4e3e-99ac-1d37c9da984b

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_115
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessP9_115 j) = true ∧ (witnessP9_115 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
