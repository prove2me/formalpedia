-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_194
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:41:57.362193+00:00
-- url     : https://prove2.me/submissions/139cb31b-d8c8-4041-b687-bd5522a64253

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_194
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_194 j) = true ∧ (witnessD8_194 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
