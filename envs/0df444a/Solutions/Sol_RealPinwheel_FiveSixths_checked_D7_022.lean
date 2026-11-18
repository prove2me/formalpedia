-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_022
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:33.867935+00:00
-- url     : https://prove2.me/submissions/0af55e42-1ff1-4daf-9151-e32e865485ca

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_022
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 15, witnessCheck (witnessD7_022 j) = true ∧ (witnessD7_022 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
