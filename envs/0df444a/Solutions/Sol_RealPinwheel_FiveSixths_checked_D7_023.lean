-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_023
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:24.51124+00:00
-- url     : https://prove2.me/submissions/3744c8af-3611-42af-929c-771e68ec2fd9

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_023
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD7_023 j) = true ∧ (witnessD7_023 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
