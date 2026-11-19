-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_195
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:46:33.52856+00:00
-- url     : https://prove2.me/submissions/841d4895-af86-4d23-a0ef-f90ca8696f94

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_195
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 22, witnessCheck (witnessD8_195 j) = true ∧ (witnessD8_195 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
