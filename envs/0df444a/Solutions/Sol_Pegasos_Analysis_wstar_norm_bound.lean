-- Prove2me | solution 1 for Pegasos.Analysis.wstar_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:40:17.447286+00:00
-- url     : https://prove2.me/submissions/3c04cabf-c1c6-4107-917f-7dbc07486edd

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

lemma hinge_convex {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    UnderstandingML.hingeLoss (a • u + b • v) (x, y) ≤
      a * UnderstandingML.hingeLoss u (x, y) + b * UnderstandingML.hingeLoss v (x, y) := by
  unfold UnderstandingML.hingeLoss
  simp only
  apply max_le
  · have h1 := le_max_left 0 (1 - y * inner ℝ u x)
    have h2 := le_max_left 0 (1 - y * inner ℝ v x)
    nlinarith [mul_nonneg ha h1, mul_nonneg hb h2]
  · have h1 := le_max_right 0 (1 - y * inner ℝ u x)
    have h2 := le_max_right 0 (1 - y * inner ℝ v x)
    rw [inner_add_left, inner_smul_left, inner_smul_left]
    simp only [conj_trivial]
    have e : 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
        = a * (1 - y * inner ℝ u x) + b * (1 - y * inner ℝ v x) := by
      have : (1 : ℝ) = a + b := hab.symm
      calc 1 - y * (a * inner ℝ u x + b * inner ℝ v x)
          = (a + b) * 1 - y * (a * inner ℝ u x + b * inner ℝ v x) := by rw [← this]; ring
        _ = _ := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma hinge_zero {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) :
    UnderstandingML.hingeLoss (0 : EuclideanSpace ℝ (Fin n)) (x, y) = 1 := by
  unfold UnderstandingML.hingeLoss
  simp

theorem solution {n m : ℕ} (lam : ℝ) (hlam : 0 < lam)
    (x : Fin m → EuclideanSpace ℝ (Fin n)) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (wstar : EuclideanSpace ℝ (Fin n)) (hwstar : ∀ w, svmObj lam x y wstar ≤ svmObj lam x y w) :
    ‖wstar‖ ≤ 1 / Real.sqrt lam := by
  have hm1 : (1 / (m : ℝ)) * (m : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : (m : ℝ) ≠ 0 := by exact_mod_cast h.ne'
      rw [one_div, inv_mul_cancel₀ this]
  have hm0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  set T := ∑ i, UnderstandingML.hingeLoss wstar (x i, y i) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => hinge_nonneg _ _ _)
  have key : ∀ s : ℝ, 0 ≤ s → s < 1 → (1 + s) * (lam * ‖wstar‖ ^ 2) ≤ 2 := by
    intro s hs0 hs1
    have hw := hwstar (s • wstar)
    unfold svmObj at hw
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow] at hw
    have hsum : ∑ i, UnderstandingML.hingeLoss (s • wstar) (x i, y i)
        ≤ s * T + (1 - s) * m := by
      have : ∑ i, UnderstandingML.hingeLoss (s • wstar) (x i, y i)
          ≤ ∑ i : Fin m, (s * UnderstandingML.hingeLoss wstar (x i, y i) + (1 - s)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have h := hinge_convex (x i) (y i) wstar 0 s (1 - s) hs0 (by linarith) (by ring)
        rw [smul_zero, add_zero, hinge_zero] at h
        linarith
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← hT, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at this
      linarith
    have h1 := mul_le_mul_of_nonneg_left hsum hm0
    have h2 : (1 / (m : ℝ)) * ((1 - s) * m) ≤ (1 - s) := by
      calc (1 / (m : ℝ)) * ((1 - s) * m) = (1 - s) * ((1 / (m : ℝ)) * m) := by ring
        _ ≤ (1 - s) * 1 := mul_le_mul_of_nonneg_left hm1 (by linarith)
        _ = 1 - s := by ring
    have hH : 0 ≤ (1 / (m : ℝ)) * T := mul_nonneg hm0 hT0
    have h3 : lam / 2 * ‖wstar‖ ^ 2 + 1 / (m : ℝ) * T
        ≤ lam / 2 * (s ^ 2 * ‖wstar‖ ^ 2) + 1 / (m : ℝ) * ∑ i, UnderstandingML.hingeLoss (s • wstar) (x i, y i) := hw
    have h4 : (1 - s) * ((1 + s) * (lam * ‖wstar‖ ^ 2)) ≤ (1 - s) * 2 := by
      nlinarith [mul_nonneg hm0 hT0, mul_le_mul_of_nonneg_left hsum hm0]
    exact le_of_mul_le_mul_left h4 (by linarith)
  have hc : lam * ‖wstar‖ ^ 2 ≤ 1 := by
    by_contra hcon
    rw [not_le] at hcon
    have hcpos : 0 < lam * ‖wstar‖ ^ 2 := by linarith
    have h := key (1 / (lam * ‖wstar‖ ^ 2)) (by positivity) (by rw [div_lt_one hcpos]; exact hcon)
    have hne : lam * ‖wstar‖ ^ 2 ≠ 0 := hcpos.ne'
    have e : (1 + 1 / (lam * ‖wstar‖ ^ 2)) * (lam * ‖wstar‖ ^ 2) = lam * ‖wstar‖ ^ 2 + 1 := by
      rw [add_mul, one_mul, one_div, inv_mul_cancel₀ hne]
    rw [e] at h
    linarith
  have hsq : (1 / Real.sqrt lam) ^ 2 = 1 / lam := by
    rw [div_pow, Real.sq_sqrt hlam.le]; simp
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [hsq, le_div_iff₀ hlam]
  linarith
