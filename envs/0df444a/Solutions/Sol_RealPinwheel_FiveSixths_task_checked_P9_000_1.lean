-- Prove2me | solution 1 for RealPinwheel.FiveSixths.task_checked_P9_000_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T05:05:57.673126+00:00
-- url     : https://prove2.me/submissions/6e37b635-5ff6-4c12-9e63-e054c5e53a85

import Definitions.Def_RealPinwheel_FiveSixths_TaskWitnessCheck
import Definitions.Def_RealPinwheel_FiveSixths_WitnessP9_000
open RealPinwheel.FiveSixths
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem solution (j : Fin 1) (i : Fin 3) : taskWitnessCheck (witnessP9_000 j) (⟨3 + i.val, by omega⟩ : Fin 9) = true := by
  fin_cases j <;> fin_cases i <;> decide +kernel
