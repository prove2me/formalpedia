-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_216
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:53.735224+00:00
-- url     : https://prove2.me/submissions/cb36359b-379c-45be-887b-23d96cebc666

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_216
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 25, witnessCheck (witnessP9_216 j) = true ∧ (witnessP9_216 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
