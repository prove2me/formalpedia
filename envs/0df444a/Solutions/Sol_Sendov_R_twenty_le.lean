-- Prove2me | solution 1 for Sendov.R_twenty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:39.578509+00:00
-- url     : https://prove2.me/submissions/92d064e1-305b-4fe3-9abe-23cafeba5b88

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
import Theorems.Thm_Sendov_M_twenty
import Theorems.Thm_Sendov_R_le_of_integral_le
import Theorems.Thm_Sendov_integral_eq_mom
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) :
    R 20 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 38 + 1 / (76 * (3 + α))
      + 1710 * A 20 α ^ 2 / (3 + α) * mom 20 α 8 := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  have hk : ((((20 : ℕ) : ℝ) - 4) / 2) = ((8 : ℕ) : ℝ) := by norm_num
  have h := R_le_of_integral_le (n := 20) (by norm_num) hα (le_of_eq (integral_eq_mom 8 hk))
  rw [M_twenty] at h
  push_cast at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring
end Sendov
