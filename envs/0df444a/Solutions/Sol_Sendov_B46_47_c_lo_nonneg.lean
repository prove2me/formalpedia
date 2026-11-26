-- Prove2me | solution 1 for Sendov.B46_47.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:39:23.789436+00:00
-- url     : https://prove2.me/submissions/be78f42b-de78-4eac-9b12-a59c58742e03

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
import Theorems.Thm_Sendov_B46_47_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
namespace Sendov.B46_47
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 46 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B46_47
