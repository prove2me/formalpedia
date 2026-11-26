-- Prove2me | solution 1 for Sendov.Q_succ_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:04.429139+00:00
-- url     : https://prove2.me/submissions/221aff5d-e357-4e02-9095-b29fd4573092

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {α t : ℝ}
namespace Sendov
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (hα : 0 ≤ α) (t : ℝ) :
    Q (n + 1) α t = Q n α t - (2 * α / ((n : ℝ) * ((n : ℝ) - 1))) * t * (1 - t) := by
  have h1 : ((n : ℝ) - 1) ≠ 0 := by
    have := M_pos hn; simp only [M] at this; linarith
  have h2 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hM1 : M (n + 1) = (n : ℝ) := by simp only [M]; push_cast; ring
  have hMn : M n = (n : ℝ) - 1 := by simp only [M]
  simp only [Q, c, A, hM1, hMn]
  field_simp
  ring
end Sendov
