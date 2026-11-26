-- Prove2me | solution 1 for Sendov.B10_11.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:22:56.48437+00:00
-- url     : https://prove2.me/submissions/3265aa46-a365-4cfa-bdcc-2ac5b3dcc5b7

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
import Theorems.Thm_Sendov_B10_11_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
namespace Sendov.B10_11
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5) : 0 ≤ c 10 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B10_11
