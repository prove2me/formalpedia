-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_031
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:42:59.737833+00:00
-- url     : https://prove2.me/submissions/47fe09e2-732c-4c73-985f-14d2a6f4a4a0

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_031
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessD7_031 j) = true ∧ (witnessD7_031 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
