-- Prove2me | solution 1 for Pegasos.Analysis.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:47:39.319258+00:00
-- url     : https://prove2.me/submissions/705d99fc-5014-4a2d-a8cb-598dc3b2aecf

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

lemma proj_nonexp {n : ℕ} (B : Set (EuclideanSpace ℝ (Fin n))) (hB : Convex ℝ B)
    (y z u : EuclideanSpace ℝ (Fin n)) (hz : LogRegretOCO.OGD.IsProj B y z) (hu : u ∈ B) :
    ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  obtain ⟨hzB, hmin⟩ := hz
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 →
      -2 * inner ℝ (z - y) (u - z) ≤ 0 + s * ‖u - z‖ ^ 2 := by
    intro s hs0 hs1
    have hp : z + s • (u - z) ∈ B := by
      have := hB hzB hu (show 0 ≤ 1 - s by linarith) hs0.le (by ring)
      have e : (1 - s) • z + s • u = z + s • (u - z) := by module
      rwa [e] at this
    have h1 := hmin _ hp
    have e2 : z + s • (u - z) - y = (z - y) + s • (u - z) := by abel
    rw [e2] at h1
    have h3 := norm_add_sq_real (z - y) (s • (u - z))
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h3
    have h4 : ‖z - y‖ ^ 2 ≤ ‖(z - y) + s • (u - z)‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h5 : s * (-2 * inner ℝ (z - y) (u - z)) ≤ s * (0 + s * ‖u - z‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h5 hs0
  have hA := le_of_small _ _ _ key
  have h3 := norm_add_sq_real (y - z) (z - u)
  rw [sub_add_sub_cancel] at h3
  have e : inner ℝ (y - z) (z - u) = inner ℝ (z - y) (u - z) := by
    rw [← inner_neg_neg, neg_sub, neg_sub]
  nlinarith [sq_nonneg ‖y - z‖]

lemma harm_eq (N : ℕ) : ∑ t ∈ Finset.Icc 1 N, (1 / (t : ℝ)) = ((harmonic N : ℚ) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
    push_cast
    ring

theorem solution {n : ℕ} (lam G : ℝ) (hlam : 0 < lam) (B : Set (EuclideanSpace ℝ (Fin n)))
    (hBclosed : IsClosed B) (hBconvex : Convex ℝ B) (T : ℕ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ) (w g : ℕ → EuclideanSpace ℝ (Fin n))
    (hf : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (fun v => f t v - lam / 2 * ‖v‖ ^ 2))
    (hw1 : w 1 ∈ B)
    (hstep : ∀ t ∈ Finset.Icc 1 T,
      LogRegretOCO.OGD.IsProj B (w t - (1 / (lam * (t : ℝ))) • g t) (w (t + 1)))
    (hg : ∀ t ∈ Finset.Icc 1 T, UnderstandingML.IsSubgradient (f t) (w t) (g t))
    (hG : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ G)
    (u : EuclideanSpace ℝ (Fin n)) (hu : u ∈ B) :
    (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, f t (w t)
      ≤ (1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, f t u
        + G ^ 2 * (1 + Real.log T) / (2 * lam * T) := by
  -- one step
  have step : ∀ t ∈ Finset.Icc 1 T, f t (w t) - f t u ≤
      lam / 2 * (((t : ℝ) - 1) * ‖w t - u‖ ^ 2 - (t : ℝ) * ‖w (t + 1) - u‖ ^ 2)
        + G ^ 2 / (2 * lam) * (1 / (t : ℝ)) := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.1 ht).1
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
    have a := strong_sub lam (f t) (hf t ht) (w t) (g t) (hg t ht) u
    have b := proj_nonexp B hBconvex _ _ u (hstep t ht) hu
    have e1 : w t - (1 / (lam * (t : ℝ))) • g t - u = (w t - u) - (1 / (lam * (t : ℝ))) • g t := by abel
    rw [e1, norm_sub_sq_real (w t - u) ((1 / (lam * (t : ℝ))) • g t), inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at b
    set s := lam * (t : ℝ) with hs
    set e := 1 / s with he
    have hspos : 0 < s := by positivity
    have hse : s * e = 1 := by rw [he]; field_simp
    set I := inner ℝ (w t - u) (g t) with hI
    set c := ‖g t‖ ^ 2 with hc
    have hcG : c ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hG t ht) 2
    have hepos : 0 ≤ e := by positivity
    have b2 := mul_le_mul_of_nonneg_left b (by positivity : 0 ≤ s / 2)
    have hse1 : s * e * I = I := by rw [hse, one_mul]
    have hse2 : s * e * (e * c) = e * c := by rw [hse, one_mul]
    have hI2 : I ≤ s / 2 * (‖w t - u‖ ^ 2 - ‖w (t + 1) - u‖ ^ 2) + e / 2 * c := by
      nlinarith [b2, hse1, hse2]
    have hec : e / 2 * c ≤ e / 2 * G ^ 2 := mul_le_mul_of_nonneg_left hcG (by positivity)
    have hee : e / 2 * G ^ 2 = G ^ 2 / (2 * lam) * (1 / (t : ℝ)) := by
      rw [he, hs]; field_simp
    have hss : s / 2 * (‖w t - u‖ ^ 2 - ‖w (t + 1) - u‖ ^ 2) =
        lam / 2 * ((t : ℝ) * ‖w t - u‖ ^ 2 - (t : ℝ) * ‖w (t + 1) - u‖ ^ 2) := by
      rw [hs]; ring
    nlinarith [a, hI2, hec, hee, hss]
  -- telescoping
  have tele : ∀ N : ℕ, N ≤ T →
      ∑ t ∈ Finset.Icc 1 N, (f t (w t) - f t u) ≤
        -(lam / 2) * (N : ℝ) * ‖w (N + 1) - u‖ ^ 2
          + G ^ 2 / (2 * lam) * ∑ t ∈ Finset.Icc 1 N, (1 / (t : ℝ)) := by
    intro N
    induction N with
    | zero => intro _; simp
    | succ N ih =>
      intro hN
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have h1 := ih (by omega)
      have h2 := step (N + 1) (Finset.mem_Icc.2 ⟨by omega, hN⟩)
      push_cast at h2 ⊢
      nlinarith [h1, h2]
  have hT : ∑ t ∈ Finset.Icc 1 T, (f t (w t) - f t u) ≤
      G ^ 2 / (2 * lam) * (1 + Real.log T) := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · subst h0; simp; positivity
    · have h1 := tele T le_rfl
      have hh : ∑ t ∈ Finset.Icc 1 T, (1 / (t : ℝ)) ≤ 1 + Real.log T := by
        rw [harm_eq]
        exact_mod_cast harmonic_le_one_add_log T
      have h2 : 0 ≤ (lam / 2) * (T : ℝ) * ‖w (T + 1) - u‖ ^ 2 := by positivity
      have h3 : 0 ≤ G ^ 2 / (2 * lam) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hh h3]
  rw [Finset.sum_sub_distrib] at hT
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast hpos
    have e : G ^ 2 * (1 + Real.log T) / (2 * lam * T) = (1 / (T : ℝ)) * (G ^ 2 / (2 * lam) * (1 + Real.log T)) := by
      field_simp
    rw [e, ← mul_add]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
