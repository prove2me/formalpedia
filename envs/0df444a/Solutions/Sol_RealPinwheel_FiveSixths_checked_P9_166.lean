-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_166
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:58.699142+00:00
-- url     : https://prove2.me/submissions/bd730d4c-e601-43f2-a65c-dda2baff78b9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_166
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_166 j) = true ∧ (witnessP9_166 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
