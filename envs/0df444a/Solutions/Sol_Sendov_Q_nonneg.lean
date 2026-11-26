-- Prove2me | solution 1 for Sendov.Q_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:42.205263+00:00
-- url     : https://prove2.me/submissions/3ea9e13b-1d98-4a32-851b-405166641859

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic
import Theorems.Thm_Sendov_Q_eq

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c n α ^ 2 ≤ A n α) (t : ℝ) : 0 ≤ Q n α t := by
  rw [Q_eq]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
end Sendov
