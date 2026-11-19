-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_178
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:31:48.801809+00:00
-- url     : https://prove2.me/submissions/5a40f04d-e7ad-4fa4-92db-656361410b16

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_178
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_178 j) = true ∧ (witnessD8_178 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
