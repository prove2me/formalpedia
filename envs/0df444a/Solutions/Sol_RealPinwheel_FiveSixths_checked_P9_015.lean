-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_015
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:26.088621+00:00
-- url     : https://prove2.me/submissions/9e79f253-0c70-4194-8a25-fb9e51e125c1

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_015
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 2, witnessCheck (witnessP9_015 j) = true ∧ (witnessP9_015 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
