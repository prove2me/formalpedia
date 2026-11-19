-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_D8_160
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T06:23:33.283044+00:00
-- url     : https://prove2.me/submissions/f5209d81-e561-46ec-b19e-5eb24fcb55ed

import Definitions.Def_RealPinwheel_FiveSixths_WitnessD8_160
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 16, witnessCheck (witnessD8_160 j) = true ∧ (witnessD8_160 j).length ≤ 608 := by
  intro j
  fin_cases j <;> decide +kernel
