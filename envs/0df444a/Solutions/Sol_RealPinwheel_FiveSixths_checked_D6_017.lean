-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D6_017
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:33:52.154634+00:00
-- url     : https://prove2.me/submissions/94315e95-5ded-4603-8237-8c375976929a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD6_017
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 36, witnessCheck (witnessD6_017 j) = true ∧ (witnessD6_017 j).length ≤ 64 := by
  intro j
  fin_cases j <;> decide +kernel
