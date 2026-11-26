-- Prove2me | solution 1 for Sendov.continuous_pow_mul_QQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:55:22.877305+00:00
-- url     : https://prove2.me/submissions/e6bc6640-9dbb-47dc-815a-1f70583c5bc2

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
import Theorems.Thm_Sendov_continuous_rpow_const


set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (c A : ℝ) (k : ℕ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ k * QQ c A t ^ e := by
  have hQ : Continuous fun t : ℝ => QQ c A t := by simp only [QQ]; fun_prop
  have hk : Continuous fun t : ℝ => t ^ k := by fun_prop
  exact hk.mul ((continuous_rpow_const he).comp hQ)
end Sendov
