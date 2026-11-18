-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_060
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:58:46.163285+00:00
-- url     : https://prove2.me/submissions/3ace2304-0e02-402b-94db-1f9d48145d0a

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_060
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 8, witnessCheck (witnessD8_060 j) = true ∧ (witnessD8_060 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
