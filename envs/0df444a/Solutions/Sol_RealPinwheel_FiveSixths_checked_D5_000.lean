-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D5_000
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T03:56:58.173176+00:00
-- url     : https://prove2.me/submissions/6c8aca41-1a0c-4c41-83ab-c0a880521d1a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_000
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 36, witnessCheck (witnessD5_000 j) = true ∧ (witnessD5_000 j).length ≤ 32 := by
  intro j
  fin_cases j <;> decide +kernel
