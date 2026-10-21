-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_yn_z
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:20:47.649234+00:00
-- url     : https://prove2.me/submissions/90bee4d0-9ad7-4b37-904c-820defdc86c6

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem prl_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    ‖(2 : ℝ) • u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_left]
  simp only [Real.norm_ofNat, RCLike.conj_to_real]
  ring

theorem prl_y_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} {F : H → H} {lam : ℝ} {x y : ℕ → H}
    (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (n : ℕ) (hn : 1 ≤ n) :
    y n = (2 : ℝ) • x n - x (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using (hrun.2 k).2

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (lam : ℝ) (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) :
    ∀ n : ℕ, 1 ≤ n →
      ‖y n - z‖ ^ 2 = 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 + 2 * ‖x n - x (n - 1)‖ ^ 2 ∧
      2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 ≤ ‖y n - z‖ ^ 2 := by
  intro n hn
  have h1 : y n - z = (2 : ℝ) • (x n - z) - (x (n - 1) - z) := by
    rw [prl_y_eq hrun n hn]; module
  have h2 : x n - z - (x (n - 1) - z) = x n - x (n - 1) := by abel
  have h3 : ‖y n - z‖ ^ 2 = 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 + 2 * ‖x n - x (n - 1)‖ ^ 2 := by
    rw [h1, prl_key, h2]
  refine ⟨h3, ?_⟩
  rw [h3]; nlinarith [sq_nonneg ‖x n - x (n - 1)‖]
