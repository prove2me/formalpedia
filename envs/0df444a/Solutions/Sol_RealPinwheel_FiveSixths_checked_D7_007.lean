-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_007
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:13:43.073063+00:00
-- url     : https://prove2.me/submissions/03aecad6-74df-45d9-8fe1-bf09caffb15f

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_007
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 9, witnessCheck (witnessD7_007 j) = true ∧ (witnessD7_007 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
