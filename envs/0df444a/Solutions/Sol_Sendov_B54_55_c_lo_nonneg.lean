-- Prove2me | solution 1 for Sendov.B54_55.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:04.470896+00:00
-- url     : https://prove2.me/submissions/d977473e-76d7-4d51-bac9-b8cb34593248

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree54_55
import Theorems.Thm_Sendov_B54_55_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B54_55
namespace Sendov.B54_55
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 54 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B54_55
