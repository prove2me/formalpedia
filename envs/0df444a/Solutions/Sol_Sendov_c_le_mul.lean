-- Prove2me | solution 1 for Sendov.c_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:46:26.475619+00:00
-- url     : https://prove2.me/submissions/9ea62146-50ca-41a5-b338-152f71b0d2be

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
import Theorems.Thm_Sendov_mul_eq_c

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ≤ a * x := by
  rw [mul_eq_c hn hα]
  simp only [c]
  have h3 : (0 : ℝ) < 3 + α := by linarith
  have : α / (2 * (3 + α)) = (α / (3 + α)) / 2 := by field_simp
  rw [this]
  linarith
end Sendov
