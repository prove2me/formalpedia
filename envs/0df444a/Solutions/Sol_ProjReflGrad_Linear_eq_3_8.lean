-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_3_8
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:25:30.351889+00:00
-- url     : https://prove2.me/submissions/46fea615-6ea2-497d-96e7-bd738235b4b4

import Mathlib
import Definitions.Def_ProjReflGrad_Linear_Setting

set_option autoImplicit false

theorem prl_y_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {C : Set H} {F : H → H} {lam : ℝ} {x y : ℕ → H}
    (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (n : ℕ) (hn : 1 ≤ n) :
    y n = (2 : ℝ) • x n - x (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simpa using (hrun.2 k).2

theorem prl_proj_char {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {C : Set H} (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (z : H) :
    ProjReflGrad.Weak.proj C z ∈ C ∧
      ∀ w ∈ C, inner ℝ (z - ProjReflGrad.Weak.proj C z) (w - ProjReflGrad.Weak.proj C z) ≤ 0 := by
  have hex : ∃ p, ProjReflGrad.Weak.IsProj C z p := by
    obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hne hCcl.isComplete hCcv z
    refine ⟨v, hv, fun q hq => ?_⟩
    rw [hvn]
    exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨q, hq⟩ : C)
  have hp : ProjReflGrad.Weak.proj C z = hex.choose := by
    unfold ProjReflGrad.Weak.proj; rw [dif_pos hex]
  have hs := hex.choose_spec
  rw [hp]
  refine ⟨hs.1, ?_⟩
  have : ‖z - hex.choose‖ = ⨅ w : C, ‖z - w‖ := by
    apply le_antisymm
    · haveI : Nonempty C := hne.to_subtype
      exact le_ciInf (fun q => hs.2 q q.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨hex.choose, hs.1⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCcv hs.1).mp this

theorem prl_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (u v : H) :
    ‖(2 : ℝ) • u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 - ‖v‖ ^ 2 + 2 * ‖u - v‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_left]
  simp only [Real.norm_ofNat, RCLike.conj_to_real]
  ring

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (F : H → H) (m lam : ℝ) (hm : 0 < m) (hC2s : ProjReflGrad.Linear.IsStronglyMonotoneMap F m)
    (hlam0 : 0 < lam) (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) :
    ∀ m1 : ℝ, 0 < m1 → m1 ≤ m → ∀ n : ℕ, 1 ≤ n →
      2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) ≤
        2 * lam * (inner ℝ (F (y n) - F z) (y n - z)
          - m1 * (2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2)) ∧
      0 ≤ 2 * lam * (inner ℝ (F (y n) - F z) (y n - z) - m * ‖y n - z‖ ^ 2) := by
  intro m1 hm1 hm1m n hn
  have hmon := hC2s (y n) z
  have h1 : y n - z = (2 : ℝ) • (x n - z) - (x (n - 1) - z) := by
    rw [prl_y_eq hrun n hn]; module
  have h2 : x n - z - (x (n - 1) - z) = x n - x (n - 1) := by abel
  have h3 : ‖y n - z‖ ^ 2 = 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 + 2 * ‖x n - x (n - 1)‖ ^ 2 := by
    rw [h1, prl_key, h2]
  set Q := 2 * ‖x n - z‖ ^ 2 - ‖x (n - 1) - z‖ ^ 2 with hQ
  have hQy : Q ≤ ‖y n - z‖ ^ 2 := by rw [h3]; nlinarith [sq_nonneg ‖x n - x (n - 1)‖]
  have hy0 : 0 ≤ ‖y n - z‖ ^ 2 := sq_nonneg _
  have h4 : m1 * Q ≤ m * ‖y n - z‖ ^ 2 := by
    rcases le_total Q 0 with hq | hq
    · nlinarith
    · nlinarith
  refine ⟨?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  · apply mul_nonneg (by positivity)
    linarith
