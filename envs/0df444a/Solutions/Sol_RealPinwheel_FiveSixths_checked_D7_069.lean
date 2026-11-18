-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_069
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:26:58.405848+00:00
-- url     : https://prove2.me/submissions/673dbe06-afbe-46e5-ab2b-ddca93f10cef

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_069
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 49, witnessCheck (witnessD7_069 j) = true ∧ (witnessD7_069 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
