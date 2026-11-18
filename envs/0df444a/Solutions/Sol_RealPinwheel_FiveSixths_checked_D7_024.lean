-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_024
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:29.739117+00:00
-- url     : https://prove2.me/submissions/17ae50ab-d047-4d7d-9194-bf397970c885

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_024
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD7_024 j) = true ∧ (witnessD7_024 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
