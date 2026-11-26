-- Prove2me | solution 1 for Sendov.R_eight_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:17:11.410231+00:00
-- url     : https://prove2.me/submissions/5f8387c2-f863-473c-917d-5b3523de8def

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree8
import Theorems.Thm_Sendov_M_eight
import Theorems.Thm_Sendov_R_le_of_integral_le
import Theorems.Thm_Sendov_integral_eq_mom
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) :
    R 8 α ≤ 1 / 6 + 1 / (4 * (3 + α)) + 1 / 14 + 1 / (28 * (3 + α))
      + 84 * A 8 α ^ 2 / (3 + α) * mom 8 α 2 := by
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  have hk : ((((8 : ℕ) : ℝ) - 4) / 2) = ((2 : ℕ) : ℝ) := by norm_num
  have h := R_le_of_integral_le (n := 8) (by norm_num) hα (le_of_eq (integral_eq_mom 2 hk))
  rw [M_eight] at h
  push_cast at h
  refine h.trans (le_of_eq ?_)
  field_simp
  ring
end Sendov
