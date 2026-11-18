-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_072
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:38:00.489673+00:00
-- url     : https://prove2.me/submissions/dd372c00-3247-4cd3-a609-bd5f8519ff31

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_072
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 64, witnessCheck (witnessD7_072 j) = true ∧ (witnessD7_072 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
