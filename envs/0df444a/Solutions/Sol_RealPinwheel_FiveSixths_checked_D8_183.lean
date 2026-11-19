-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_183
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:34:51.282665+00:00
-- url     : https://prove2.me/submissions/46c383f2-c5e6-4107-bb5e-477818863f16

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_183
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD8_183 j) = true ∧ (witnessD8_183 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
