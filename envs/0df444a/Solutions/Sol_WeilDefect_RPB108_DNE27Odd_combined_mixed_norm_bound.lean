-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Odd.combined_mixed_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:22:24.668193+00:00
-- url     : https://prove2.me/submissions/2520d3d8-0317-44ce-82b4-c35161705406

import Theorems.Thm_WeilDefect_RPB108_DNE27Odd_mixed_root_certificate
import Theorems.Thm_WeilDefect_RPB108_sqrt_add_le_of_squared_certificate
import Definitions.Def_RPB108_DNE27MixedEnergy_Odd
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Odd
theorem solution :
    Real.sqrt nativeDualSquare + Real.sqrt highMixedSquare ≤ mixedUpper := by
  obtain ⟨ha,hb,hM,he,hc⟩ := mixed_root_certificate
  exact sqrt_add_le_of_squared_certificate _ _ _ ha hb hM he hc
