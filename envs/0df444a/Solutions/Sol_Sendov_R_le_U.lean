-- Prove2me | solution 1 for Sendov.R_le_U
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:42.474949+00:00
-- url     : https://prove2.me/submissions/400d204f-96bf-48dd-ad22-092bf11dc2d7

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
import Theorems.Thm_Sendov_integral_le_tail
import Theorems.Thm_Sendov_R_le_of_integral_le


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 5 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α) (hc : 0 < c n α) :
    R n α ≤ U n α := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hr : (0 : ℝ) < ((n : ℝ) - 4) / 2 := by linarith
  exact R_le_of_integral_le (by omega) hα (integral_le_tail (by omega) hα hfeas hc hr)
end Sendov
