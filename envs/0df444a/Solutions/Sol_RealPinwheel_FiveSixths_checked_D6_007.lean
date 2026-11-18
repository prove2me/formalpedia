-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_007
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:25:26.830277+00:00
-- url     : https://prove2.me/submissions/920c273b-de67-4a29-a509-7d06837c042f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_007
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 30, witnessCheck (witnessD6_007 j) = true ∧ (witnessD6_007 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
