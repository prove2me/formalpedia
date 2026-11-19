-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_289
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:28:12.4272+00:00
-- url     : https://prove2.me/submissions/65906b21-c551-4db6-97c5-ee78d7ae4098

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_289
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 45, witnessCheck (witnessP9_289 j) = true ∧ (witnessP9_289 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
