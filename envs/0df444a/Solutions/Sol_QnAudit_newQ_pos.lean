-- Prove2me | solution 1 for QnAudit.newQ_pos
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:10:15.352195+00:00
-- url     : https://prove2.me/submissions/cedeb735-f654-4bf3-ba3b-28a919c895a4

import Mathlib
import Definitions.Def_RHPF28_QnAudit_e1481adb3874
import Theorems.Thm_QnAudit_moment_pos
open MeasureTheory Set
open QnAudit

theorem solution (K : ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hK : ∀ t > 0, 0 < K t)
    (hi : IntegrableOn (fun t => weight x n t * K t) (Ioi 0)) :
    0 < newQ K x n := by
  have hfac : (0 : ℝ) < (Nat.factorial (n - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n - 1)
  exact mul_pos (div_pos (pow_pos hx _) hfac) (moment_pos K x n hK hi)
