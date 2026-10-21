-- Prove2me | solution 1 for ProjReflGrad.Linear.eq_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:25:28.119169+00:00
-- url     : https://prove2.me/submissions/d5bbd2cc-e830-45ba-9c75-c665df79904c

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

theorem prl_exp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (a p z f : H) (lam : ℝ) :
    ‖a - lam • f - z‖ ^ 2 - ‖a - lam • f - p‖ ^ 2 =
      ‖a - z‖ ^ 2 - ‖p - a‖ ^ 2 - 2 * lam * inner ℝ f (p - z) := by
  have e1 : a - lam • f - z = (a - z) - lam • f := by abel
  have e2 : a - lam • f - p = (a - p) - lam • f := by abel
  have e4 : inner ℝ (a - z) f - inner ℝ (a - p) f = inner ℝ (p - z) f := by
    rw [← inner_sub_left]; congr 1; abel
  rw [e1, e2, norm_sub_sq_real (a - z), norm_sub_sq_real (a - p), norm_sub_rev p a,
    real_inner_comm (p - z) f]
  simp only [inner_smul_right]
  linear_combination (-2 * lam) * e4

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (lam : ℝ)
    (x y : ℕ → H) (hrun : ProjReflGrad.Weak.IsPRGRun C F lam x y) (z : H) (hz : z ∈ C) :
    ∀ n : ℕ,
      ‖x (n + 1) - z‖ ^ 2 ≤
          ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 ∧
        ‖x n - lam • F (y n) - z‖ ^ 2 - ‖x n - lam • F (y n) - x (n + 1)‖ ^ 2 =
          ‖x n - z‖ ^ 2 - ‖x (n + 1) - x n‖ ^ 2 - 2 * lam * inner ℝ (F (y n)) (x (n + 1) - z) := by
  intro n
  have hp : x (n + 1) = ProjReflGrad.Weak.proj C (x n - lam • F (y n)) := (hrun.2 n).1
  obtain ⟨-, hvi⟩ := prl_proj_char hCcl hCcv ⟨z, hz⟩ (x n - lam • F (y n))
  rw [← hp] at hvi
  have h := hvi z hz
  refine ⟨?_, prl_exp (x n) (x (n + 1)) z (F (y n)) lam⟩
  generalize x (n + 1) = p at h
  generalize x n - lam • F (y n) = u at h
  have e : u - z = (u - p) + (p - z) := by abel
  have e2 : p - z = -(z - p) := by abel
  have h3 : ‖u - z‖ ^ 2 = ‖u - p‖ ^ 2 + 2 * inner ℝ (u - p) (p - z) + ‖p - z‖ ^ 2 := by
    rw [e, norm_add_sq_real]
  have h4 : inner ℝ (u - p) (p - z) = - inner ℝ (u - p) (z - p) := by
    rw [e2, inner_neg_right]
  nlinarith
