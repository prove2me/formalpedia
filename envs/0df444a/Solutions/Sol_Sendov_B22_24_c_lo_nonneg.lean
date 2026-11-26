-- Prove2me | solution 1 for Sendov.B22_24.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:18.23005+00:00
-- url     : https://prove2.me/submissions/fc18b04b-09aa-4b1e-b65c-1770f6621d80

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree22_24
import Theorems.Thm_Sendov_B22_24_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B22_24
namespace Sendov.B22_24
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 23 / 2) : 0 ≤ c 22 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B22_24
