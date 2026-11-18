-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_021
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:38:32.660946+00:00
-- url     : https://prove2.me/submissions/8db5f811-60fa-4a26-b68f-a58e507e6296

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_021
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 4, witnessCheck (witnessD8_021 j) = true ∧ (witnessD8_021 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
