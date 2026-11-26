-- Prove2me | solution 1 for Sendov.Q_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:54.038412+00:00
-- url     : https://prove2.me/submissions/bcb6273d-faed-4fe6-87be-2120f9437910

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch
import Theorems.Thm_Sendov_Q_succ_sub
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {α t : ℝ}
namespace Sendov
theorem _root_.solution {m n : ℕ} (hm : 2 ≤ m) (h : m ≤ n) (hα : 0 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Q n α t ≤ Q m α t := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := by omega
      have hn2 : 2 ≤ n := le_trans hm hmn
      have hstep : Q (n + 1) α t ≤ Q n α t := by
        rw [Q_succ_sub n hn2 hα t]
        have hnn : (0 : ℝ) ≤ 2 * α / ((n : ℝ) * ((n : ℝ) - 1)) := by
          have h1 : (0 : ℝ) < (n : ℝ) - 1 := by
            have := M_pos hn2; simp only [M] at this; linarith
          have h2 : (0 : ℝ) < (n : ℝ) := by linarith
          positivity
        nlinarith [mul_nonneg (mul_nonneg hnn ht0) (by linarith : (0 : ℝ) ≤ 1 - t)]
      exact le_trans hstep (ih hmn)
    · have : m = n + 1 := by omega
      subst this
      exact le_rfl
end Sendov
