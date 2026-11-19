-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_174
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:29:58.411996+00:00
-- url     : https://prove2.me/submissions/31778035-5e32-4b18-8817-f676ce6530a5

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_174
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD8_174 j) = true ∧ (witnessD8_174 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
