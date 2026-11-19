-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_028
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:16:35.936211+00:00
-- url     : https://prove2.me/submissions/15a5c6bc-5222-4343-a1c4-393ed493eb9a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_028
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 5, witnessCheck (witnessD8_028 j) = true ∧ (witnessD8_028 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
