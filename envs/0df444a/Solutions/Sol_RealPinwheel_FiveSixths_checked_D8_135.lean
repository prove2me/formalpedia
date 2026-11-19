-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_135
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:59:12.638365+00:00
-- url     : https://prove2.me/submissions/d3f9e802-3b28-4bd0-a184-fa8dff28eac4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_135
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 14, witnessCheck (witnessD8_135 j) = true ∧ (witnessD8_135 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
