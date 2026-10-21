-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_3_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:25:29.267664+00:00
-- url     : https://prove2.me/submissions/582dda68-9791-4bcb-998a-419bdd2d01eb

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

theorem prl_34 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (w d g : H) (lam : ℝ)
    (h1 : inner ℝ (w - lam • g) d ≤ 0) (h2 : inner ℝ (w - lam • g) w ≤ 0) :
    2 * lam * inner ℝ g (-w - d) ≤ ‖d‖ ^ 2 - ‖w‖ ^ 2 - ‖d + w‖ ^ 2 := by
  rw [norm_add_sq_real]
  have c1 := real_inner_comm w d
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_neg_right,
    real_inner_self_eq_norm_sq, RCLike.conj_to_real] at h1 h2 ⊢
  nlinarith

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hne : C.Nonempty) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) :
    ∀ n : ℕ, 2 ≤ n →
      2 * lam * inner ℝ (F (y (n - 1))) (y n - x (n + 1)) ≤
        ‖x (n + 1) - x n‖ ^ 2 - ‖x n - y n‖ ^ 2 - ‖x (n + 1) - y n‖ ^ 2 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have hyn : y (k + 2) = (2 : ℝ) • x (k + 2) - x (k + 1) := (hrun.2 (k + 1)).2
  have hb : x (k + 2) = ProjReflGrad.Weak.proj C (x (k + 1) - lam • F (y (k + 1))) := (hrun.2 (k + 1)).1
  obtain ⟨hbC, hvi⟩ := prl_proj_char hCcl hCcv hne (x (k + 1) - lam • F (y (k + 1)))
  rw [← hb] at hbC hvi
  have haC : x (k + 1) ∈ C := by
    have := (prl_proj_char hCcl hCcv hne (x k - lam • F (y k))).1
    rwa [← (hrun.2 k).1] at this
  have hcC : x (k + 3) ∈ C := by
    have := (prl_proj_char hCcl hCcv hne (x (k + 2) - lam • F (y (k + 2)))).1
    rwa [← (hrun.2 (k + 2)).1] at this
  have h1 := hvi _ hcC
  have h2 := hvi _ haC
  have := prl_34 (x (k + 1) - x (k + 2)) (x (k + 3) - x (k + 2)) (F (y (k + 1))) lam
    (by have e : x (k + 1) - x (k + 2) - lam • F (y (k + 1)) = x (k + 1) - lam • F (y (k + 1)) - x (k + 2) := by abel
        rw [e]; exact h1)
    (by have e : x (k + 1) - x (k + 2) - lam • F (y (k + 1)) = x (k + 1) - lam • F (y (k + 1)) - x (k + 2) := by abel
        have e' : x (k + 1) - x (k + 2) = x (k + 1) - x (k + 2) := rfl
        rw [e]; exact h2)
  have e1 : y (k + 2) - x (k + 2 + 1) = -(x (k + 1) - x (k + 2)) - (x (k + 3) - x (k + 2)) := by
    rw [hyn]; module
  have e2 : x (k + 2) - y (k + 2) = x (k + 1) - x (k + 2) := by rw [hyn]; module
  have e3 : x (k + 2 + 1) - y (k + 2) = (x (k + 3) - x (k + 2)) + (x (k + 1) - x (k + 2)) := by
    rw [hyn]; module
  rw [e1, e2, e3]
  exact this
