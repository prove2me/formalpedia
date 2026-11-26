-- Prove2me | solution 1 for Sendov.B20_22.c_lo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:27:06.247418+00:00
-- url     : https://prove2.me/submissions/3be14814-c41b-4e29-9932-17e5d54bc711

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
import Theorems.Thm_Sendov_B20_22_c_lo
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
namespace Sendov.B20_22
theorem _root_.solution {α : ℝ} (hα : 0 ≤ α) (hU : α ≤ 21 / 2) : 0 ≤ c 20 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  rw [c_lo hα]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hα (sub_nonneg.2 hU), sq_nonneg α]
end Sendov.B20_22
