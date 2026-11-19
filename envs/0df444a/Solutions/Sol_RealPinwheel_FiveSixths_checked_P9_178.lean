-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_178
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:07:58.241105+00:00
-- url     : https://prove2.me/submissions/2ced14f4-974a-4535-ac9e-9d6ea3dda4ed

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_178
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 19, witnessCheck (witnessP9_178 j) = true ∧ (witnessP9_178 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
