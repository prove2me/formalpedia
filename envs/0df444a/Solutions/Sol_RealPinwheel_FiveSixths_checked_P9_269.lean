-- Prove2me | solution 1 for RealPinwheel.FiveSixths.checked_P9_269
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:15:07.581435+00:00
-- url     : https://prove2.me/submissions/778d255d-e2ed-435f-a031-ae2bbb5f7cd7

import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_269
open RealPinwheel.FiveSixths
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem solution : ∀ j : Fin 38, witnessCheck (witnessP9_269 j) = true ∧ (witnessP9_269 j).length ≤ 1800 := by
  intro j
  fin_cases j <;> decide +kernel
