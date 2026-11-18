-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_022
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:38:13.864643+00:00
-- url     : https://prove2.me/submissions/2f008ba4-f510-478e-88cf-fb6dbb0c6462

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_022
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_022 j) = true ∧ (witnessD8_022 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
