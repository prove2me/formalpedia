-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_035
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:45:18.403978+00:00
-- url     : https://prove2.me/submissions/16abed5e-6a50-4971-9d83-cb7e36682c56

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_035
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 20, witnessCheck (witnessD7_035 j) = true ∧ (witnessD7_035 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
