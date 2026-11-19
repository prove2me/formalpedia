-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_096
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:27:11.819796+00:00
-- url     : https://prove2.me/submissions/500be020-323d-4ac9-8c3a-a5a3541e3916

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_096
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessP9_096 j) = true ∧ (witnessP9_096 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
