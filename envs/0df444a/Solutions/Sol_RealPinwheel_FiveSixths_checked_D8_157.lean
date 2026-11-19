-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_157
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:18:13.8962+00:00
-- url     : https://prove2.me/submissions/478abbaa-ac25-411b-bb84-5eb28555f506

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_157
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_157 j) = true ∧ (witnessD8_157 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
