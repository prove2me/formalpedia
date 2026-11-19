-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_242
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:52:34.455636+00:00
-- url     : https://prove2.me/submissions/a23a08f4-0691-4258-bfd5-375d2ee9ef10

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_242
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 31, witnessCheck (witnessP9_242 j) = true ∧ (witnessP9_242 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
