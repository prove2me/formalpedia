-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_133
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:20:24.275995+00:00
-- url     : https://prove2.me/submissions/2b577274-88ae-4fb9-adea-7a188b094ad0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_133
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessP9_133 j) = true ∧ (witnessP9_133 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
