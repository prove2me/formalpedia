-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_192
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:42:35.372125+00:00
-- url     : https://prove2.me/submissions/eedd9d21-c18d-4bfa-8cbb-61ed7cf59d68

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_192
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessD8_192 j) = true ∧ (witnessD8_192 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
