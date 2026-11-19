-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_167
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:26:51.161188+00:00
-- url     : https://prove2.me/submissions/104c4af4-9edd-480b-b177-720bf808827e

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_167
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD8_167 j) = true ∧ (witnessD8_167 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
