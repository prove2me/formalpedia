-- Prove2me | solution 1 for Sendov.mul_eq_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:45:26.146059+00:00
-- url     : https://prove2.me/submissions/3319bedf-20a1-4b3d-bf90-6bb1293d29b7

import Definitions.Def_Sendov_Reduction_BetaBound
import Definitions.Def_Sendov_Reduction_Stat
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    a * x = 1 - QQ (a * x) (a ^ 2) 1 / 2 - α / M n := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [QQ, hα]
  field_simp
  ring
end Sendov
