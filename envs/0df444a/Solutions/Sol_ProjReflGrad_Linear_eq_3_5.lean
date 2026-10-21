-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:20:48.815117+00:00
-- url     : https://prove2.me/submissions/bfdd76f4-27b0-4b28-a464-96420e501dc1

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem prl_amgm (r A B s : ℝ) (hr : r ^ 2 = 2) (hr1 : 1 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s) :
    2 * (A + B) * s ≤ (1 + r) * A ^ 2 + B ^ 2 + r * s ^ 2 := by
  have h1 : 0 ≤ (r - 1) * ((r + 1) * A - s) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have h2 : (r - 1) * ((r + 1) * A - s) ^ 2 =
      (r + 1) * A ^ 2 - 2 * A * s + (r - 1) * s ^ 2 := by
    linear_combination ((r + 1) * A ^ 2 - 2 * A * s) * hr
  nlinarith [sq_nonneg (B - s)]

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (L lam : ℝ) (hL : 0 < L) (hC3 : ProjReflGrad.Weak.IsLipschitzMap F L) (hlam0 : 0 < lam)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 1 ≤ n →
      2 * lam * inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤
        lam * L * (1 + Real.sqrt 2) * ‖y n - x n‖ ^ 2 + lam * L * ‖x n - y (n - 1)‖ ^ 2
          + Real.sqrt 2 * lam * L * ‖x (n + 1) - y n‖ ^ 2 := by
  intro n _
  have hr : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  set A := ‖y n - x n‖
  set B := ‖x n - y (n - 1)‖
  set s := ‖x (n + 1) - y n‖
  have hkey := prl_amgm (Real.sqrt 2) A B s hr hr1 (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  have hd : y n - y (n - 1) = (y n - x n) + (x n - y (n - 1)) := by abel
  have h1 : ‖F (y n) - F (y (n - 1))‖ ≤ L * (A + B) := by
    calc ‖F (y n) - F (y (n - 1))‖ ≤ L * ‖y n - y (n - 1)‖ := hC3 _ _
      _ ≤ L * (A + B) := by
        apply mul_le_mul_of_nonneg_left _ hL.le
        rw [hd]; exact norm_add_le _ _
  have h2 : inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤ L * (A + B) * s := by
    calc _ ≤ ‖F (y n) - F (y (n - 1))‖ * ‖y n - x (n + 1)‖ := real_inner_le_norm _ _
      _ ≤ L * (A + B) * s := by
        rw [norm_sub_rev (y n) (x (n + 1))]
        exact mul_le_mul h1 le_rfl (norm_nonneg _) (by positivity)
  have h3 : 2 * lam * inner ℝ (F (y n) - F (y (n - 1))) (y n - x (n + 1)) ≤
      2 * lam * (L * (A + B) * s) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : lam * L * (2 * (A + B) * s) ≤ lam * L * ((1 + Real.sqrt 2) * A ^ 2 + B ^ 2 + Real.sqrt 2 * s ^ 2) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  nlinarith [h3, h4]
