-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:22:00.67528+00:00
-- url     : https://prove2.me/submissions/520df84b-f3cd-4c77-b647-f281162201e2

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_000
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 3, witnessCheck (witnessD7_000 j) = true ∧ (witnessD7_000 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
