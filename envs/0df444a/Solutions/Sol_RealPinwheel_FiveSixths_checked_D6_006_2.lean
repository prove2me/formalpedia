-- Prove2me | solution 2 for RealPinwheel.FiveSixths.checked_D6_006
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:55:32.810066+00:00
-- url     : https://prove2.me/submissions/1956109b-da60-41bd-8d98-3d75280a9708

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_006
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 29, witnessCheck (witnessD6_006 j) = true ∧ (witnessD6_006 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
