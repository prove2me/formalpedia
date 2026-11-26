-- Prove2me | solution 1 for Sendov.B6_6.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:21:05.656314+00:00
-- url     : https://prove2.me/submissions/cbdf550f-ec80-48df-83cb-4c5ba2ebd3ae

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
import Theorems.Thm_Sendov_B6_6_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
namespace Sendov.B6_6
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 5 / 2) : 0 ≤ c 6 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B6_6
