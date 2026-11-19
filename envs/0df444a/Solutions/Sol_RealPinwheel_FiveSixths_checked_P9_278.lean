-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_278
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:21:05.975544+00:00
-- url     : https://prove2.me/submissions/bcc019a6-497d-49cc-bcff-5134e6a67413

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_278
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 41, witnessCheck (witnessP9_278 j) = true ∧ (witnessP9_278 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
