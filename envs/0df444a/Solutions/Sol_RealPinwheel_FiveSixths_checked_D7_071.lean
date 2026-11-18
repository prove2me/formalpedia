-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_071
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:39:06.700959+00:00
-- url     : https://prove2.me/submissions/aa7b1e3d-9916-4277-8607-900ca0496e54

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_071
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 58, witnessCheck (witnessD7_071 j) = true ∧ (witnessD7_071 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
