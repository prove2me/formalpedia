-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_013
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:46.69923+00:00
-- url     : https://prove2.me/submissions/2503dd3e-6fec-4b13-b2c4-a1ea482ab830

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_013
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 11, witnessCheck (witnessD7_013 j) = true ∧ (witnessD7_013 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
