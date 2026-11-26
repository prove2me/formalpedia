-- Prove2me | solution 1 for Sendov.QQ_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:11.63181+00:00
-- url     : https://prove2.me/submissions/59e63565-bd68-4eae-9d7e-edee4fb219fa

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
import Theorems.Thm_Sendov_QQ_eq

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by
  rw [QQ_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
end Sendov
