-- Prove2me | solution 1 for ProjReflGrad.Weak.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:45:59.772146+00:00
-- url     : https://prove2.me/submissions/45f50007-552d-4981-b443-3256b82b21ac

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

set_option autoImplicit false

open ProjReflGrad.Weak

lemma proj_spec {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Set H) (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M) (x : H) :
    proj M x ∈ M ∧ ∀ w ∈ M, inner ℝ (x - proj M x) (w - proj M x) ≤ 0 := by
  classical
  have hex : ∃ p, IsProj M x p := by
    obtain ⟨v, hv, hvn⟩ := exists_norm_eq_iInf_of_complete_convex hMne hMcl.isComplete hMcv x
    refine ⟨v, hv, fun q hq => ?_⟩
    rw [hvn]
    exact ciInf_le (⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ : BddBelow (Set.range fun w : M => ‖x - w‖)) ⟨q, hq⟩
  have hp : IsProj M x (proj M x) := by
    unfold proj
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨hp.1, ?_⟩
  have : ‖x - proj M x‖ = ⨅ w : M, ‖x - w‖ := by
    haveI : Nonempty M := hMne.to_subtype
    apply le_antisymm
    · exact le_ciInf (fun w => hp.2 w w.2)
    · exact ciInf_le (⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ : BddBelow (Set.range fun w : M => ‖x - w‖)) ⟨proj M x, hp.1⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hMcv hp.1).mp this

lemma proj_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Set H) (hMne : M.Nonempty) (hMcl : IsClosed M) (hMcv : Convex ℝ M) (x y : H) (hy : y ∈ M) :
    ‖proj M x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖x - proj M x‖ ^ 2 := by
  obtain ⟨_, hp⟩ := proj_spec M hMne hMcl hMcv x
  have h1 := hp y hy
  have h2 := norm_add_sq_real (x - proj M x) (proj M x - y)
  have h3 : x - proj M x + (proj M x - y) = x - y := by abel
  have h4 : inner ℝ (x - proj M x) (proj M x - y) = - inner ℝ (x - proj M x) (y - proj M x) := by
    rw [← inner_neg_right, neg_sub]
  rw [h3, h4] at h2
  nlinarith [h1, h2]

lemma I3_aux {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v a b : H) (lam : ℝ)
    (c1 : inner ℝ (-a - lam • v) b ≤ 0) (c2 : inner ℝ (-a - lam • v) (-a) ≤ 0) :
    lam * inner ℝ v (a - b) ≤ inner ℝ a b - ‖a‖ ^ 2 := by
  rw [inner_sub_left, inner_neg_left, real_inner_smul_left] at c1
  rw [inner_sub_left, inner_neg_left, inner_neg_right, inner_neg_right, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at c2
  rw [inner_sub_right]
  nlinarith [c1, c2]

lemma vec_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v w xn xp xq yn yp z : H) (lam L : ℝ) (hlam : 0 < lam) (hL : 0 < L)
    (hyn : yn = (2:ℝ) • xn - xp)
    (ha : ‖xq - z‖ ^ 2 ≤ ‖xn - lam • u - z‖ ^ 2 - ‖xn - lam • u - xq‖ ^ 2)
    (hm : 0 ≤ inner ℝ (u - w) (yn - z))
    (c1 : inner ℝ (xp - lam • v - xn) (xq - xn) ≤ 0)
    (c2 : inner ℝ (xp - lam • v - xn) (xp - xn) ≤ 0)
    (hlip : ‖u - v‖ ≤ L * ‖yn - yp‖) :
    ‖xq - z‖ ^ 2 ≤ ‖xn - z‖ ^ 2 - (1 - lam * L * (1 + Real.sqrt 2)) * ‖xn - xp‖ ^ 2
        + lam * L * ‖xn - yp‖ ^ 2 - (1 - Real.sqrt 2 * lam * L) * ‖xq - yn‖ ^ 2
        - 2 * lam * inner ℝ w (yn - z) := by
  have I1 : ‖xq - z‖ ^ 2 ≤ ‖xn - z‖ ^ 2 - ‖xq - xn‖ ^ 2 + 2 * (lam * inner ℝ u (z - xq)) := by
    have e1 : xn - lam • u - z = (xn - z) - lam • u := by abel
    have e2 : xn - lam • u - xq = (xn - xq) - lam • u := by abel
    have n1 := norm_sub_sq_real (xn - z) (lam • u)
    have n2 := norm_sub_sq_real (xn - xq) (lam • u)
    rw [e1, e2, n1, n2, norm_sub_rev xn xq] at ha
    have k1 : inner ℝ (xn - xq) (lam • u) - inner ℝ (xn - z) (lam • u) = lam * inner ℝ u (z - xq) := by
      rw [← inner_sub_left]
      have : (xn - xq) - (xn - z) = z - xq := by abel
      rw [this, real_inner_smul_right, real_inner_comm]
    linarith
  have I2 : inner ℝ u (z - xq) ≤ - inner ℝ w (yn - z) + inner ℝ (u - v) (yn - xq) + inner ℝ v (yn - xq) := by
    have h1 : inner ℝ u (z - xq) = inner ℝ u (z - yn) + inner ℝ u (yn - xq) := by
      rw [← inner_add_right]; congr 1; abel
    have h2 : inner ℝ u (z - yn) = - inner ℝ u (yn - z) := by
      rw [← inner_neg_right, neg_sub]
    have h3 : inner ℝ u (yn - xq) = inner ℝ (u - v) (yn - xq) + inner ℝ v (yn - xq) := by
      rw [inner_sub_left]; ring
    rw [inner_sub_left] at hm
    linarith
  have he : yn - xq = (xn - xp) - (xq - xn) := by rw [hyn, two_smul]; abel
  have I3 : lam * inner ℝ v (yn - xq) ≤ inner ℝ (xn - xp) (xq - xn) - ‖xn - xp‖ ^ 2 := by
    have r1 : xp - lam • v - xn = -(xn - xp) - lam • v := by abel
    have r2 : xp - xn = -(xn - xp) := by abel
    rw [r1] at c1 c2
    rw [r2] at c2
    rw [he]
    exact I3_aux v (xn - xp) (xq - xn) lam c1 c2
  have I4 : inner ℝ (u - v) (yn - xq) ≤ L * (‖xn - xp‖ + ‖xn - yp‖) * ‖yn - xq‖ := by
    have h1 : yn - yp = (xn - xp) + (xn - yp) := by rw [hyn, two_smul]; abel
    have h2 : ‖yn - yp‖ ≤ ‖xn - xp‖ + ‖xn - yp‖ := by rw [h1]; exact norm_add_le _ _
    calc inner ℝ (u - v) (yn - xq) ≤ ‖u - v‖ * ‖yn - xq‖ := real_inner_le_norm _ _
      _ ≤ (L * ‖yn - yp‖) * ‖yn - xq‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg _)
      _ ≤ (L * (‖xn - xp‖ + ‖xn - yp‖)) * ‖yn - xq‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left h2 hL.le
  have I5 : ‖yn - xq‖ ^ 2 = ‖xn - xp‖ ^ 2 - 2 * inner ℝ (xn - xp) (xq - xn) + ‖xq - xn‖ ^ 2 := by
    rw [he, norm_sub_sq_real]
  have hr : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have Y1 : 2 * ‖xn - xp‖ * ‖yn - xq‖ ≤ (1 + Real.sqrt 2) * ‖xn - xp‖ ^ 2 + (Real.sqrt 2 - 1) * ‖yn - xq‖ ^ 2 := by
    have h0 : 0 ≤ (1 + Real.sqrt 2) * (‖xn - xp‖ - (Real.sqrt 2 - 1) * ‖yn - xq‖) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have hid : (1 + Real.sqrt 2) * (‖xn - xp‖ - (Real.sqrt 2 - 1) * ‖yn - xq‖) ^ 2
        = (1 + Real.sqrt 2) * ‖xn - xp‖ ^ 2 - 2 * ‖xn - xp‖ * ‖yn - xq‖
          + (Real.sqrt 2 - 1) * ‖yn - xq‖ ^ 2 := by
      have hr2 : Real.sqrt 2 ^ 2 = 2 := by rw [sq]; exact hr
      linear_combination (-2 * ‖xn - xp‖ * ‖yn - xq‖ + (Real.sqrt 2 - 1) * ‖yn - xq‖ ^ 2) * hr2
    linarith
  have Y2 : 2 * ‖xn - yp‖ * ‖yn - xq‖ ≤ ‖xn - yp‖ ^ 2 + ‖yn - xq‖ ^ 2 := by
    nlinarith [sq_nonneg (‖xn - yp‖ - ‖yn - xq‖)]
  have hlL : 0 ≤ lam * L := mul_nonneg hlam.le hL.le
  have F1 := mul_le_mul_of_nonneg_left I2 hlam.le
  have F2 := mul_le_mul_of_nonneg_left I4 hlam.le
  have F3 := mul_le_mul_of_nonneg_left Y1 hlL
  have F4 := mul_le_mul_of_nonneg_left Y2 hlL
  rw [norm_sub_rev xq yn]
  nlinarith [I1, I3, I5, F1, F2, F3, F4]

lemma prg_core {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam : ℝ)
    (hC2 : IsMonotoneMap F) (hL : 0 < L) (hC3 : IsLipschitzMap F L) (hlam0 : 0 < lam)
    (x y : ℕ → H) (hrun : IsPRGRun C F lam x y) (z : H) (hz : z ∈ solSet C F) (k : ℕ) :
    ‖x (k + 3) - z‖ ^ 2 ≤ ‖x (k + 2) - z‖ ^ 2
        - (1 - lam * L * (1 + Real.sqrt 2)) * ‖x (k + 2) - x (k + 1)‖ ^ 2
        + lam * L * ‖x (k + 2) - y (k + 1)‖ ^ 2
        - (1 - Real.sqrt 2 * lam * L) * ‖x (k + 3) - y (k + 2)‖ ^ 2
        - 2 * lam * inner ℝ (F z) (y (k + 2) - z) := by
  have hne : C.Nonempty := ⟨z, hz.1⟩
  obtain ⟨_, hrec⟩ := hrun
  have hxq : x (k + 3) = proj C (x (k + 2) - lam • F (y (k + 2))) := (hrec (k + 2)).1
  have hxn : x (k + 2) = proj C (x (k + 1) - lam • F (y (k + 1))) := (hrec (k + 1)).1
  have hxp : x (k + 1) = proj C (x k - lam • F (y k)) := (hrec k).1
  have hyn : y (k + 2) = (2:ℝ) • x (k + 2) - x (k + 1) := (hrec (k + 1)).2
  have hxpC : x (k + 1) ∈ C := by rw [hxp]; exact (proj_spec C hne hCcl hCcv _).1
  have hxnC : x (k + 2) ∈ C := by rw [hxn]; exact (proj_spec C hne hCcl hCcv _).1
  have hxqC : x (k + 3) ∈ C := by rw [hxq]; exact (proj_spec C hne hCcl hCcv _).1
  have ha := proj_ineq C hne hCcl hCcv (x (k + 2) - lam • F (y (k + 2))) z hz.1
  rw [← hxq] at ha
  have hspec := (proj_spec C hne hCcl hCcv (x (k + 1) - lam • F (y (k + 1)))).2
  rw [← hxn] at hspec
  exact vec_key (F (y (k + 2))) (F (y (k + 1))) (F z) (x (k + 2)) (x (k + 1)) (x (k + 3))
    (y (k + 2)) (y (k + 1)) z lam L hlam0 hL hyn ha (hC2 _ _) (hspec _ hxqC) (hspec _ hxpC) (hC3 _ _)

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (F : H → H) (L lam : ℝ)
    (hC2 : IsMonotoneMap F) (hL : 0 < L) (hC3 : IsLipschitzMap F L) (hlam0 : 0 < lam)
    (x y : ℕ → H) (hrun : IsPRGRun C F lam x y) (z : H) (hz : z ∈ solSet C F) :
    ∀ n : ℕ, 2 ≤ n →
      ‖x (n + 1) - z‖ ^ 2 ≤ ‖x n - z‖ ^ 2
        - (1 - lam * L * (1 + Real.sqrt 2)) * ‖x n - x (n - 1)‖ ^ 2
        + lam * L * ‖x n - y (n - 1)‖ ^ 2
        - (1 - Real.sqrt 2 * lam * L) * ‖x (n + 1) - y n‖ ^ 2
        - 2 * lam * inner ℝ (F z) (y n - z) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  exact prg_core C hCcl hCcv F L lam hC2 hL hC3 hlam0 x y hrun z hz k
