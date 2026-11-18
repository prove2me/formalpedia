-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_061
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:23.686961+00:00
-- url     : https://prove2.me/submissions/1b58ba0c-782d-4e34-b21d-4e070be06436

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_061
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_061 j) = true ∧ (witnessD8_061 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
