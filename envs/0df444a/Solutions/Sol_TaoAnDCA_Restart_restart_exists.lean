-- Prove2me | solution 1 for TaoAnDCA.Restart.restart_exists
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:49:58.632765+00:00
-- url     : https://prove2.me/submissions/c9381e46-31ae-417a-8588-76f0d959baad

import Mathlib
import Definitions.Def_TaoAnDCA_Restart_Setting

open TaoAnDCA.TRS

theorem quadratic_identity {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (mu : ℝ) (y : EuclideanSpace ℝ (Fin n)) (hy : A y + mu • y = -b)
    (x : EuclideanSpace ℝ (Fin n)) :
    quad A b x = quad A b y - mu / 2 * (‖x‖ ^ 2 - ‖y‖ ^ 2)
      + 1 / 2 * inner ℝ (x - y) (A (x - y) + mu • (x - y)) := by
  have hb : b = -(A y + mu • y) := by rw [hy]; simp
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) x y
  simp only [quad, hb, map_sub, inner_add_right, inner_sub_left,
    inner_sub_right, inner_neg_left, inner_add_left, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hcross : inner ℝ y (A x) = inner ℝ (A y) x := by
    calc
      _ = inner ℝ (A x) y := real_inner_comm _ _
      _ = inner ℝ x (A y) := hs
      _ = inner ℝ (A y) x := real_inner_comm _ _
  rw [hcross]
  simp only [real_inner_comm y x, real_inner_comm (A y) x, real_inner_comm (A y) y]
  ring

theorem norm_shift_sq {n : ℕ} (x u : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖x + t • u‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * inner ℝ x u + t ^ 2 * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm u x,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem eigen_shift_cost {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b xs u : EuclideanSpace ℝ (Fin n)) (mu lam t : ℝ)
    (hk : A xs + mu • xs = -b) (hu : A u = lam • u) :
    quad A b (xs + t • u) = quad A b xs - mu / 2 * (‖xs + t • u‖ ^ 2 - ‖xs‖ ^ 2)
      + 1 / 2 * t ^ 2 * (mu + lam) * ‖u‖ ^ 2 := by
  rw [quadratic_identity A hA b mu xs hk]
  simp only [add_sub_cancel_left, map_smul, hu, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem restart_direction {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b xs v : EuclideanSpace ℝ (Fin n)) (r mu : ℝ)
    (hk : IsKKT A b r xs mu)
    (hn : inner ℝ v (A v + mu • v) < 0) (hd : inner ℝ xs v ≠ 0) :
    ∃ xbar : EuclideanSpace ℝ (Fin n), ‖xbar‖ ≤ r ∧ quad A b xbar < quad A b xs := by
  have hv : v ≠ 0 := by intro h; simp [h] at hn
  let t := -2 * inner ℝ xs v / ‖v‖ ^ 2
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hnv)
  have ht : t ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hd) hnv2
  have hsq : ‖xs + t • v‖ ^ 2 = ‖xs‖ ^ 2 := by
    rw [norm_shift_sq]
    dsimp [t]
    field_simp
    <;> ring
  have he : ‖xs + t • v‖ = ‖xs‖ := by nlinarith [norm_nonneg xs, norm_nonneg (xs + t • v)]
  refine ⟨xs + t • v, by rw [he]; exact hk.2.2.2, ?_⟩
  rw [quadratic_identity A hA b mu xs hk.2.1, hsq]
  have hi : inner ℝ (xs + t • v - xs) (A (xs + t • v - xs) + mu • (xs + t • v - xs)) =
      t ^ 2 * inner ℝ v (A v + mu • v) := by
    simp only [add_sub_cancel_left, map_smul, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    ring
  rw [hi]
  have hh := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht) hn
  nlinarith

theorem solution {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r)
    (xs : EuclideanSpace ℝ (Fin n)) (lamStar : ℝ) (hkkt : TaoAnDCA.TRS.IsKKT A b r xs lamStar)
    (lam1 : ℝ) (u : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) (hAu : A u = lam1 • u) (hneg : lamStar + lam1 < 0) :
    ∃ xbar : EuclideanSpace ℝ (Fin n), ‖xbar‖ ≤ r ∧ TaoAnDCA.TRS.quad A b xbar < TaoAnDCA.TRS.quad A b xs := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hquad : inner ℝ u (A u + lamStar • u) < 0 := by
    rw [hAu]
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have h := mul_neg_of_neg_of_pos hneg (sq_pos_of_pos hnu)
    nlinarith
  by_cases hx : xs = 0
  · subst xs
    have hm : lamStar = 0 := by
      have hc := hkkt.2.2.1
      simp only [norm_zero, zero_sub, mul_neg, neg_eq_zero] at hc
      exact (mul_eq_zero.mp hc).resolve_right (ne_of_gt hr)
    have hb : b = 0 := by simpa [hm] using hkkt.2.1.symm
    subst b
    let t := r / ‖u‖
    have ht : 0 < t := div_pos hr hnu
    refine ⟨t • u, ?_, ?_⟩
    · simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      dsimp [t]
      rw [div_mul_cancel₀ _ (ne_of_gt hnu)]
    · simp only [quad, inner_zero_left, add_zero, map_smul, hAu,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
        map_zero, inner_zero_right]
      have hl : lam1 < 0 := by simpa [hm] using hneg
      have h := mul_neg_of_pos_of_neg (sq_pos_of_pos ht) hl
      have h' := mul_neg_of_neg_of_pos h (sq_pos_of_pos hnu)
      nlinarith
  · by_cases hd : inner ℝ xs u = 0
    · let f : ℝ → ℝ := fun t => inner ℝ (u + t • xs) (A (u + t • xs) + lamStar • (u + t • xs))
      have hf : Continuous f := by
        dsimp [f]
        fun_prop
      have hf0 : f 0 < 0 := by simpa [f] using hquad
      have hev : ∀ᶠ t in nhds (0 : ℝ), f t < 0 := hf.continuousAt.eventually (gt_mem_nhds hf0)
      obtain ⟨e, he, hef⟩ := Metric.eventually_nhds_iff.mp hev
      have ht : dist (e / 2) (0 : ℝ) < e := by rw [Real.dist_eq]; simp [abs_of_pos (by linarith : 0 < e / 2)]; linarith
      apply restart_direction A hA b xs (u + (e / 2) • xs) r lamStar hkkt (hef ht)
      simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hd, zero_add]
      exact mul_ne_zero (ne_of_gt (by linarith : 0 < e / 2)) (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
    · exact restart_direction A hA b xs u r lamStar hkkt hquad hd

#print axioms solution

