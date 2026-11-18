-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D7_027
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T04:37:33.461108+00:00
-- url     : https://prove2.me/submissions/18ac0fea-7562-4f13-8bd2-80611a61c22c

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD7_027
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessD7_027 j) = true ∧ (witnessD7_027 j).length ≤ 352 := by
  intro j
  fin_cases j <;> decide +kernel
