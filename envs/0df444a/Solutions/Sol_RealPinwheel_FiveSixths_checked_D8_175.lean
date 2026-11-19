-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_175
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:30:32.258501+00:00
-- url     : https://prove2.me/submissions/0a58bb3c-7d6b-4af3-a1c1-b8cb284d17af

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_175
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessD8_175 j) = true ∧ (witnessD8_175 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
