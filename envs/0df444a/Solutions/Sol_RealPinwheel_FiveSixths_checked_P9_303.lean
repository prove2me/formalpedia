-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_303
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:33:56.968253+00:00
-- url     : https://prove2.me/submissions/65f26dbc-a66a-4515-bce7-afe1b601be24

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_303
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 52, witnessCheck (witnessP9_303 j) = true ∧ (witnessP9_303 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
