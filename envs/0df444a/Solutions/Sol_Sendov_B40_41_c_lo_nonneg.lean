-- Prove2me | solution 1 for Sendov.B40_41.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:36:42.594953+00:00
-- url     : https://prove2.me/submissions/09ed19dc-46d0-4204-9426-f7be74831b07

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree40_41
import Theorems.Thm_Sendov_B40_41_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B40_41
namespace Sendov.B40_41
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 17) : 0 ≤ c 40 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B40_41
