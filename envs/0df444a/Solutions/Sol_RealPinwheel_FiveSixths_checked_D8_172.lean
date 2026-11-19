-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_172
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:30:41.542159+00:00
-- url     : https://prove2.me/submissions/ee3b50fc-a892-4f62-b25e-8fc6c79c983e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_172
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD8_172 j) = true ∧ (witnessD8_172 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
