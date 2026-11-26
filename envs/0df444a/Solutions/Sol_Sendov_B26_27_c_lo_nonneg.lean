-- Prove2me | solution 1 for Sendov.B26_27.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:29:43.089343+00:00
-- url     : https://prove2.me/submissions/5b06cbc1-4a28-4b0b-bc5b-086c625747d9

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
import Theorems.Thm_Sendov_B26_27_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
namespace Sendov.B26_27
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 13) : 0 ≤ c 26 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B26_27
