-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_224
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T07:09:27.693504+00:00
-- url     : https://prove2.me/submissions/0ddf52f9-cb53-4290-99cb-d2e83fda82cc

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_224
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessD8_224 j) = true ∧ (witnessD8_224 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
