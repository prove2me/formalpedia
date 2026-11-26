-- Prove2me | solution 1 for Sendov.feasible_of_beta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:36.35385+00:00
-- url     : https://prove2.me/submissions/8703cbcb-4f43-46b0-b0b8-bf4948f77758

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
import Theorems.Thm_Sendov_c_le_mul
import Theorems.Thm_Sendov_A_eq_sq
import Theorems.Thm_Sendov_alpha_le_half
import Theorems.Thm_Sendov_c_pos_of_le_half_M


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hx : x ^ 2 ≤ 1)
    (hα : α = M n * (1 - a ^ 2) / 2) (hα0 : 0 < α)
    (hbeta : QQ (a * x) (a ^ 2) 1 ≤ α / (3 + α)) : c n α ^ 2 ≤ A n α := by
  have hcpos : 0 < c n α := c_pos_of_le_half_M hn hα0.le (alpha_le_half hn hα)
  have hcle : c n α ≤ a * x := c_le_mul hn hα hα0 hbeta
  rw [A_eq_sq hn hα]
  nlinarith [hcpos, hcle, sq_nonneg a, sq_nonneg x]
end Sendov
