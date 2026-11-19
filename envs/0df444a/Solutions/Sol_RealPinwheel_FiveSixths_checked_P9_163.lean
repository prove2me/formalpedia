-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_163
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:02:53.272869+00:00
-- url     : https://prove2.me/submissions/b0a81092-c114-439a-a91f-7b259d792c28

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_163
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 17, witnessCheck (witnessP9_163 j) = true ∧ (witnessP9_163 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
