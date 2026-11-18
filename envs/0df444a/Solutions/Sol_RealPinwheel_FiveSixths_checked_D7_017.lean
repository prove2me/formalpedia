-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_017
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:26:25.172702+00:00
-- url     : https://prove2.me/submissions/068eb78d-c1e5-4e10-923e-fecd5238aa70

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_017
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 13, witnessCheck (witnessD7_017 j) = true ∧ (witnessD7_017 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
