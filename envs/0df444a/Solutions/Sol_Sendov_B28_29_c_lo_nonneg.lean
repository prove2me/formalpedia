-- Prove2me | solution 1 for Sendov.B28_29.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:30:23.193434+00:00
-- url     : https://prove2.me/submissions/acbcf271-1380-490d-9acf-d63d2ebc40b8

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree28_29
import Theorems.Thm_Sendov_B28_29_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B28_29
namespace Sendov.B28_29
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 14) : 0 ≤ c 28 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B28_29
