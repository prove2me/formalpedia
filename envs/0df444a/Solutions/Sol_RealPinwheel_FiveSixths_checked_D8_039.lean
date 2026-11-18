-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_039
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:48:04.587411+00:00
-- url     : https://prove2.me/submissions/7f9fe54a-3db3-4592-9408-1ca4bfe99450

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_039
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessD8_039 j) = true ∧ (witnessD8_039 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
