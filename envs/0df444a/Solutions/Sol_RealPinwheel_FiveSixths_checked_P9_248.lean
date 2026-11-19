-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_248
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:03:51.641737+00:00
-- url     : https://prove2.me/submissions/e7e27581-63df-4f97-8f4a-bd7baaecb869

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_248
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 32, witnessCheck (witnessP9_248 j) = true ∧ (witnessP9_248 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
