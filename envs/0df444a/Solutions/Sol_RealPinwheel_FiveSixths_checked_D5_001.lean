-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D5_001
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:01:41.241297+00:00
-- url     : https://prove2.me/submissions/46fffb70-1aaa-4746-bb03-6bbabff281c4

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD5_001
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 50, witnessCheck (witnessD5_001 j) = true ∧ (witnessD5_001 j).length ≤ 32 := by
  intro j
  fin_cases j <;> decide +kernel
