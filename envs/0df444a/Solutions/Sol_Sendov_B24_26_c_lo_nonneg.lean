-- Prove2me | solution 1 for Sendov.B24_26.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:28:53.87099+00:00
-- url     : https://prove2.me/submissions/dda03fba-8ba1-4edf-8a99-614aef94a932

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree24_26
import Theorems.Thm_Sendov_B24_26_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B24_26
namespace Sendov.B24_26
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 25 / 2) : 0 ≤ c 24 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B24_26
