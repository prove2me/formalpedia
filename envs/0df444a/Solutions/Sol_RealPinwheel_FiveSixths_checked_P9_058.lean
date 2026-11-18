-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_058
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:40:26.485976+00:00
-- url     : https://prove2.me/submissions/23332bdd-d344-4ffb-9549-f7b10c8cf0a3

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_058
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 6, witnessCheck (witnessP9_058 j) = true ∧ (witnessP9_058 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
