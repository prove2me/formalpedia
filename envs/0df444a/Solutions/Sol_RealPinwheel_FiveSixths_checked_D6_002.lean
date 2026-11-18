-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_002
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:08:19.101002+00:00
-- url     : https://prove2.me/submissions/29ac1039-d887-4963-96dc-77859520969f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_002
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 21, witnessCheck (witnessD6_002 j) = true ∧ (witnessD6_002 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
