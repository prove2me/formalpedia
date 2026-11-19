-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_172
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:00:20.702326+00:00
-- url     : https://prove2.me/submissions/bad12c94-759e-4ca1-b921-1eded37e6448

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_172
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 18, witnessCheck (witnessP9_172 j) = true ∧ (witnessP9_172 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
