-- Prove2me | solution 1 for Sendov.B32_33.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:32:50.017097+00:00
-- url     : https://prove2.me/submissions/e224a6a4-5c30-422b-9ffb-f47134541f56

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
import Theorems.Thm_Sendov_B32_33_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
namespace Sendov.B32_33
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 16) : 0 ≤ c 32 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B32_33
