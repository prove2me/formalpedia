-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_062
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:14:14.970597+00:00
-- url     : https://prove2.me/submissions/c7b821fe-ed66-4c4d-a76f-eb603f691d67

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_062
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 35, witnessCheck (witnessD7_062 j) = true ∧ (witnessD7_062 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
