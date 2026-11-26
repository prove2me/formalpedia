-- Prove2me | solution 1 for Sendov.B18_20.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:26:57.670934+00:00
-- url     : https://prove2.me/submissions/7950a541-93e7-497e-ae0c-c0c32fc897bc

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
import Theorems.Thm_Sendov_B18_20_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
namespace Sendov.B18_20
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 19 / 2) : 0 ≤ c 18 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B18_20
