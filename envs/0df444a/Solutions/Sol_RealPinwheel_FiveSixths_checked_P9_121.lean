-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_121
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:06:57.72122+00:00
-- url     : https://prove2.me/submissions/ef224c54-305c-4f43-8608-88fd3a155c56

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_121
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 12, witnessCheck (witnessP9_121 j) = true ∧ (witnessP9_121 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
