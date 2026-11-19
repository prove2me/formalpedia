-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_191
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:15:19.079253+00:00
-- url     : https://prove2.me/submissions/1c4ead9e-8404-4afd-8e33-e40e529e581a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_191
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessP9_191 j) = true ∧ (witnessP9_191 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
