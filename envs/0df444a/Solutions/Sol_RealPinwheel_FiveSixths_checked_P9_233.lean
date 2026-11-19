-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_233
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:53:54.809563+00:00
-- url     : https://prove2.me/submissions/f2d28744-4ef9-4a3b-aed5-434493668836

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_233
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 28, witnessCheck (witnessP9_233 j) = true ∧ (witnessP9_233 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
