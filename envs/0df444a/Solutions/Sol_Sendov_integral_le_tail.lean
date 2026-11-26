-- Prove2me | solution 1 for Sendov.integral_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:54.807631+00:00
-- url     : https://prove2.me/submissions/8071edb0-7017-43eb-a1a0-10826e02a340

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
import Theorems.Thm_Sendov_c_le_one
import Theorems.Thm_Sendov_Q_eq_QQ
import Theorems.Thm_Sendov_Q_one
import Theorems.Thm_Sendov_integral_le_tail_cube


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) (hfeas : c n α ^ 2 ≤ A n α)
    (hc : 0 < c n α) {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ r)
      ≤ 6 / (c n α ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4)))
        + (α / (3 + α)) ^ r / 4 := by
  have h := integral_le_tail_cube hfeas hc (c_le_one hn hα) hr
  rw [← Q_one hn hα]
  simpa only [Q_eq_QQ] using h
end Sendov
