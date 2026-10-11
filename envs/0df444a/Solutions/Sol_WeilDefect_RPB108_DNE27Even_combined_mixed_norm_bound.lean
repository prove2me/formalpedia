-- Prove2me | solution 1 for WeilDefect.RPB108.DNE27Even.combined_mixed_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:19:29.678788+00:00
-- url     : https://prove2.me/submissions/7749aa6c-1cdf-4b96-8290-86c8be3a9481

import Theorems.Thm_WeilDefect_RPB108_DNE27Even_mixed_root_certificate
import Theorems.Thm_WeilDefect_RPB108_sqrt_add_le_of_squared_certificate
import Definitions.Def_RPB108_DNE27MixedEnergy_Even
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108 WeilDefect.RPB108.DNE27Even
theorem solution :
    Real.sqrt nativeDualSquare + Real.sqrt highMixedSquare ≤ mixedUpper := by
  obtain ⟨ha,hb,hM,he,hc⟩ := mixed_root_certificate
  exact sqrt_add_le_of_squared_certificate _ _ _ ha hb hM he hc
