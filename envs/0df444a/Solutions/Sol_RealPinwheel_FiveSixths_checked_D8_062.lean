-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_062
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:59:18.874272+00:00
-- url     : https://prove2.me/submissions/d5316bb8-8139-4a10-b68a-02f44cb28cde

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_062
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_062 j) = true ∧ (witnessD8_062 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
