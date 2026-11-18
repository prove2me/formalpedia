-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:18:15.337202+00:00
-- url     : https://prove2.me/submissions/7992b54c-c026-4013-b503-c5c3e63089d1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_000
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 1, witnessCheck (witnessD8_000 j) = true ∧ (witnessD8_000 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
