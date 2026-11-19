-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_327
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:49:05.567332+00:00
-- url     : https://prove2.me/submissions/89743922-260b-492c-81cf-e05d0728042a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_327
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 83, witnessCheck (witnessP9_327 j) = true ∧ (witnessP9_327 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
