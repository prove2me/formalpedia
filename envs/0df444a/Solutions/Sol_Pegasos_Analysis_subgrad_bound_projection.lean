-- Prove2me | solution 1 for Pegasos.Analysis.subgrad_bound_projection
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:46:25.066766+00:00
-- url     : https://prove2.me/submissions/2ed2b26b-3068-415e-90b1-dc6f8e266cb1

import Mathlib
import Definitions.Def_Pegasos_Analysis_Model

set_option autoImplicit false

open Pegasos.Analysis
open scoped InnerProductSpace

namespace PEGAux

lemma quad_ineq {n : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (u w : EuclideanSpace ℝ (Fin n)) :
    lam / 2 * ‖w‖ ^ 2 + lam * inner ℝ (u - w) w ≤ lam / 2 * ‖u‖ ^ 2 := by
  have h := norm_add_sq_real w (u - w)
  rw [add_sub_cancel] at h
  rw [h, real_inner_comm]
  nlinarith [mul_nonneg hlam (sq_nonneg ‖u - w‖)]

lemma hinge_sub {n : ℕ} (w u x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    UnderstandingML.hingeLoss w (x, y)
      + (if y * inner ℝ w x < 1 then -(y * inner ℝ (u - w) x) else 0)
      ≤ UnderstandingML.hingeLoss u (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  split_ifs with h
  · rw [max_eq_right (by linarith), inner_sub_left]
    have := le_max_right 0 (1 - y * inner ℝ u x)
    linarith
  · rw [max_eq_left (by linarith)]
    simp

lemma hinge_nonneg {n : ℕ} (w x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    0 ≤ UnderstandingML.hingeLoss w (x, y) := by
  unfold UnderstandingML.hingeLoss
  exact le_max_left _ _

lemma le_of_small (A C D : ℝ) (h : ∀ s : ℝ, 0 < s → s ≤ 1 → A ≤ C + s * D) : A ≤ C := by
  have ht : Filter.Tendsto (fun s : ℝ => C + s * D) (nhdsWithin 0 (Set.Ioi 0)) (nhds C) := by
    have : Filter.Tendsto (fun s : ℝ => C + s * D) (nhds 0) (nhds (C + 0 * D)) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  exact h s hs.1 hs.2.le

lemma strong_sub {n : ℕ} (lam : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ConvexOn ℝ Set.univ (fun v => f v - lam / 2 * ‖v‖ ^ 2))
    (w g : EuclideanSpace ℝ (Fin n)) (hg : UnderstandingML.IsSubgradient f w g)
    (u : EuclideanSpace ℝ (Fin n)) :
    f w - f u + lam / 2 * ‖w - u‖ ^ 2 ≤ inner ℝ (w - u) g := by
  have hnorm : ‖u‖ ^ 2 = ‖w‖ ^ 2 + 2 * inner ℝ w (u - w) + ‖u - w‖ ^ 2 := by
    have := norm_add_sq_real w (u - w)
    rwa [add_sub_cancel] at this
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (inner ℝ (u - w) g - lam * inner ℝ w (u - w) - (f u - lam / 2 * ‖u‖ ^ 2)
        + (f w - lam / 2 * ‖w‖ ^ 2)) ≤ 0 + s * (lam / 2 * ‖u - w‖ ^ 2) := by
    intro s hs0 hs1
    have hc := hf.2 (Set.mem_univ w) (Set.mem_univ u) (show 0 ≤ 1 - s by linarith) hs0.le
      (by ring)
    simp only [smul_eq_mul] at hc
    have hp : (1 - s) • w + s • u = w + s • (u - w) := by module
    have hg' := hg ((1 - s) • w + s • u)
    have hpw : (1 - s) • w + s • u - w = s • (u - w) := by module
    rw [hpw, inner_smul_left] at hg'
    simp only [conj_trivial] at hg'
    rw [hp] at hc
    have h3 := norm_add_sq_real w (s • (u - w))
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h3
    rw [hp] at hg'
    have h4 : s * (inner ℝ (u - w) g - lam * inner ℝ w (u - w) - (f u - lam / 2 * ‖u‖ ^ 2)
        + (f w - lam / 2 * ‖w‖ ^ 2)) ≤ s * (0 + s * (lam / 2 * ‖u - w‖ ^ 2)) := by
      rw [h3] at hc
      nlinarith [hc, hg']
    exact le_of_mul_le_mul_left h4 hs0
  have hA := le_of_small _ _ _ key
  have e1 : ‖w - u‖ = ‖u - w‖ := norm_sub_rev w u
  have e2 : inner ℝ (w - u) g = - inner ℝ (u - w) g := by
    rw [← inner_neg_left, neg_sub]
  have h5 : lam / 2 * ‖u‖ ^ 2
      = lam / 2 * (‖w‖ ^ 2 + 2 * inner ℝ w (u - w) + ‖u - w‖ ^ 2) := by rw [hnorm]
  rw [e1, e2]
  linarith [hA, h5]

lemma R_nonneg {n m k : ℕ} (hk : 0 < k) (R : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (hR : ∀ i, ‖x i‖ ≤ R) (B : Fin k → Fin m) : 0 ≤ R :=
  le_trans (norm_nonneg _) (hR (B ⟨0, hk⟩))

lemma hingeTerm_norm {n m k : ℕ} (hk : 0 < k) (R : ℝ) (x : Fin m → EuclideanSpace ℝ (Fin n))
    (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1) (hR : ∀ i, ‖x i‖ ≤ R) (B : Fin k → Fin m)
    (w : EuclideanSpace ℝ (Fin n)) : ‖hingeTerm x y B w‖ ≤ R := by
  have hR0 := R_nonneg hk R x hR B
  unfold hingeTerm
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hs : ‖∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖ ≤ k * R := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j, ‖(if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖
        ≤ ∑ _j : Fin k, R := by
          refine Finset.sum_le_sum (fun j _ => ?_)
          split_ifs
          · rw [norm_smul, Real.norm_eq_abs]
            rcases hy (B j) with h | h <;> simp [h, hR (B j)]
          · simpa using hR0
      _ = k * R := by simp
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  calc 1 / (k : ℝ) * ‖∑ j, (if y (B j) * inner ℝ w (x (B j)) < 1 then y (B j) • x (B j) else 0)‖
      ≤ 1 / (k : ℝ) * (k * R) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = R := by field_simp

lemma run_sum {n m k : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (A : ℕ → Fin k → Fin m)
    (t : ℕ) (ht : 1 ≤ t) :
    run lam x y A false (t + 1)
      = (1 / (lam * (t : ℝ))) • ∑ i ∈ Finset.Icc 1 t, hingeTerm x y (A i) (run lam x y A false i) := by
  induction t, ht using Nat.le_induction with
  | base =>
    have h1 : run lam x y A false 1 = 0 := rfl
    have h2 : run lam x y A false (0 + 2) = run lam x y A false 1
        - (1 / (lam * ((0 + 1 : ℕ) : ℝ))) • subgrad lam x y (A (0 + 1)) (run lam x y A false 1) := rfl
    show run lam x y A false (0 + 2) = _
    rw [h2, h1]
    simp [subgrad, h1]
  | succ t ht ih =>
    have h2 : run lam x y A false (t + 2) = run lam x y A false (t + 1)
        - (1 / (lam * ((t + 1 : ℕ) : ℝ))) • subgrad lam x y (A (t + 1)) (run lam x y A false (t + 1)) := rfl
    show run lam x y A false (t + 2) = _
    rw [h2, Finset.sum_Icc_succ_top (by omega), subgrad]
    have htne : (t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast ht
      exact this.ne'
    have hlne : lam ≠ 0 := hlam.ne'
    have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    generalize run lam x y A false (t + 1) = w at ih ⊢
    generalize ∑ i ∈ Finset.Icc 1 t, hingeTerm x y (A i) (run lam x y A false i) = S at ih ⊢
    generalize hingeTerm x y (A (t + 1)) w = H
    rw [ih]
    match_scalars <;> field_simp <;> ring

lemma projBall_norm_le {n : ℕ} (lam : ℝ) (hlam : 0 < lam) (v : EuclideanSpace ℝ (Fin n)) :
    ‖projBall lam v‖ ≤ 1 / Real.sqrt lam := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  unfold projBall
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_min zero_le_one (by positivity))]
  by_cases hv : ‖v‖ = 0
  · rw [hv]; simpa using hr.le
  · calc min 1 (1 / Real.sqrt lam / ‖v‖) * ‖v‖ ≤ (1 / Real.sqrt lam / ‖v‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = 1 / Real.sqrt lam := div_mul_cancel₀ _ hv

end PEGAux

open PEGAux

theorem solution {n m k : ℕ} (lam R : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hR : ∀ i, ‖x i‖ ≤ R) (A : ℕ → Fin k → Fin m) (t : ℕ) (ht : 1 ≤ t) :
    ‖run lam x y A true t‖ ≤ 1 / Real.sqrt lam ∧
      ‖subgrad lam x y (A t) (run lam x y A true t)‖ ≤ Real.sqrt lam + R := by
  have hr : 0 < 1 / Real.sqrt lam := by positivity
  have hw : ‖run lam x y A true t‖ ≤ 1 / Real.sqrt lam := by
    rcases Nat.eq_or_lt_of_le ht with h | h
    · subst h
      have : run lam x y A true 1 = 0 := rfl
      rw [this, norm_zero]; exact hr.le
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
      have e : run lam x y A true (s + 2) = projBall lam (run lam x y A true (s + 1)
          - (1 / (lam * ((s + 1 : ℕ) : ℝ))) • subgrad lam x y (A (s + 1)) (run lam x y A true (s + 1))) := rfl
      rw [e]
      exact projBall_norm_le lam hlam _
  refine ⟨hw, ?_⟩
  unfold subgrad
  calc ‖lam • run lam x y A true t - hingeTerm x y (A t) (run lam x y A true t)‖
      ≤ ‖lam • run lam x y A true t‖ + ‖hingeTerm x y (A t) (run lam x y A true t)‖ :=
        norm_sub_le _ _
    _ ≤ Real.sqrt lam + R := by
        refine add_le_add ?_ (hingeTerm_norm hk R x y hy hR _ _)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam]
        calc lam * ‖run lam x y A true t‖ ≤ lam * (1 / Real.sqrt lam) :=
              mul_le_mul_of_nonneg_left hw hlam.le
          _ = Real.sqrt lam := by
              have h := Real.sq_sqrt hlam.le
              have hs : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.2 hlam).ne'
              field_simp
              nlinarith [h]
