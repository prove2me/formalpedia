-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:02:32.342649+00:00
-- url     : https://prove2.me/submissions/2ff4c4c2-a281-4fcf-a33b-dbda63fe55a4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_000
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD6_000 j) = true ∧ (witnessD6_000 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
