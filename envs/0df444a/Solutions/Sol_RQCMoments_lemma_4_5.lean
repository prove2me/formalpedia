-- Prove2me | solution 1 for RQCMoments.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T05:04:57.461922+00:00
-- url     : https://prove2.me/submissions/7a7174bc-31d4-4162-bd09-c86e69d3d5ec

import Mathlib

set_option autoImplicit false

open Polynomial

namespace RQCMoments

lemma step_mul (a k : ℝ) (hk : 0 ≤ k) (n : ℕ) (q : ℝ[X])
    (hq : ∃ r s : ℝ[X], r.natDegree ≤ n ∧ s.natDegree ≤ n ∧ q = r ^ 2 + s ^ 2) :
    ∃ r s : ℝ[X], r.natDegree ≤ n + 1 ∧ s.natDegree ≤ n + 1 ∧
      ((X - C a) ^ 2 + C k) * q = r ^ 2 + s ^ 2 := by
  obtain ⟨r, s, hr, hs, rfl⟩ := hq
  have hw : C (Real.sqrt k) * C (Real.sqrt k) = C k := by
    rw [← C_mul, Real.mul_self_sqrt hk]
  have hd : ∀ u : ℝ[X], u.natDegree ≤ n → ((X - C a) * u).natDegree ≤ n + 1 := by
    intro u hu
    refine (natDegree_mul_le).trans ?_
    have : (X - C a : ℝ[X]).natDegree ≤ 1 := by compute_degree
    omega
  have hc : ∀ u : ℝ[X], u.natDegree ≤ n → (C (Real.sqrt k) * u).natDegree ≤ n + 1 := by
    intro u hu
    exact (natDegree_C_mul_le _ _).trans (by omega)
  refine ⟨(X - C a) * r - C (Real.sqrt k) * s, C (Real.sqrt k) * r + (X - C a) * s,
    (natDegree_sub_le _ _).trans (max_le (hd _ hr) (hc _ hs)),
    (natDegree_add_le _ _).trans (max_le (hc _ hr) (hd _ hs)), ?_⟩
  linear_combination (-(r ^ 2 + s ^ 2)) * hw

lemma exists_factor (p : ℝ[X]) (hp : ∀ t : ℝ, 0 ≤ p.eval t) (h0 : p ≠ 0)
    (hd : p.natDegree ≠ 0) :
    ∃ a k : ℝ, 0 ≤ k ∧ ∃ q : ℝ[X], (∀ t : ℝ, 0 ≤ q.eval t) ∧
      p = ((X - C a) ^ 2 + C k) * q := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, aeval z p = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ p (by
      intro h; exact hd (natDegree_eq_of_degree_eq_some h))
  by_cases him : z.im = 0
  · -- real root
    have hz' : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    set a := z.re with ha
    have hroot : p.eval a = 0 := by
      have : aeval (a : ℂ) p = ((p.eval a : ℝ) : ℂ) := by
        rw [show ((a:ℂ)) = algebraMap ℝ ℂ a from rfl, aeval_algebraMap_apply_eq_algebraMap_eval]; rfl
      rw [hz'] at hz
      rw [this] at hz
      exact_mod_cast hz
    obtain ⟨q1, hq1⟩ := dvd_iff_isRoot.mpr hroot
    have hmin : IsLocalMin (fun t => p.eval t) a := by
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only [hroot]; exact hp t
    have hder := hmin.deriv_eq_zero
    have hq1a : q1.eval a = 0 := by
      have : p.derivative.eval a = 0 := by
        rw [← Polynomial.deriv]; exact hder
      rw [hq1] at this
      simpa using this
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hq1a
    refine ⟨a, 0, le_rfl, q, ?_, ?_⟩
    · have hpq : ∀ t : ℝ, p.eval t = (t - a) ^ 2 * q.eval t := by
        intro t; rw [hq1, hq]; simp; ring
      have hne : ∀ t : ℝ, t ≠ a → 0 ≤ q.eval t := by
        intro t ht
        have h1 : 0 < (t - a) ^ 2 := by
          have : t - a ≠ 0 := sub_ne_zero.mpr ht
          positivity
        have := hp t
        rw [hpq t] at this
        exact nonneg_of_mul_nonneg_right this h1
      intro t
      by_cases ht : t = a
      · rw [ht]
        by_contra hqa
        have hqa' : q.eval a < 0 := not_le.mp hqa
        have hc : ContinuousAt (fun t => q.eval t) a := q.continuous.continuousAt
        have hev : ∀ᶠ x in nhds a, q.eval x < 0 := hc.eventually (gt_mem_nhds hqa')
        have hev2 : ∀ᶠ x in nhdsWithin a {a}ᶜ, q.eval x < 0 ∧ x ≠ a :=
          (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
        obtain ⟨x, hx1, hx2⟩ := hev2.exists
        exact absurd (hne x hx2) (not_le.mpr hx1)
      · exact hne t ht
    · rw [hq1, hq]; simp; ring
  · have hdvd := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero p hz him
    obtain ⟨u, hu⟩ := hdvd
    have hm : (X ^ 2 - C (2 * z.re) * X + C (‖z‖ ^ 2) : ℝ[X]) =
        (X - C z.re) ^ 2 + C (z.im ^ 2) := by
      have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [this]; simp only [C_add, C_mul, C_pow, map_ofNat]; ring
    refine ⟨z.re, z.im ^ 2, sq_nonneg _, u, ?_, by rw [← hm]; exact hu⟩
    intro t
    have h1 := hp t
    rw [hu, hm] at h1
    simp only [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at h1
    have h2 : 0 < (t - z.re) ^ 2 + z.im ^ 2 := by
      have : z.im ^ 2 > 0 := by positivity
      positivity
    exact nonneg_of_mul_nonneg_right h1 h2

lemma main (n : ℕ) : ∀ p : ℝ[X], (∀ t : ℝ, 0 ≤ p.eval t) → p.natDegree ≤ 2 * n →
    ∃ r s : ℝ[X], r.natDegree ≤ n ∧ s.natDegree ≤ n ∧ p = r ^ 2 + s ^ 2 := by
  induction n with
  | zero =>
    intro p hp hd
    have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    have h0 : 0 ≤ p.coeff 0 := by
      have := hp 0
      rw [hpc] at this; simpa using this
    refine ⟨C (Real.sqrt (p.coeff 0)), 0, by simp, by simp, ?_⟩
    rw [hpc]
    simp only [coeff_C_zero, map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, add_zero]
    rw [← C_pow, Real.sq_sqrt h0]
  | succ n ih =>
    intro p hp hd
    by_cases h0 : p = 0
    · exact ⟨0, 0, by simp, by simp, by simp [h0]⟩
    by_cases hd0 : p.natDegree = 0
    · have hpc : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero (by omega)
      have hc : 0 ≤ p.coeff 0 := by
        have := hp 0
        rw [hpc] at this; simpa using this
      refine ⟨C (Real.sqrt (p.coeff 0)), 0, by simp, by simp, ?_⟩
      rw [hpc]
      simp only [coeff_C_zero, map_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]
      rw [← C_pow, Real.sq_sqrt hc]
    obtain ⟨a, k, hk, q, hq, hpq⟩ := exists_factor p hp h0 hd0
    have hq0 : q ≠ 0 := by rintro rfl; simp at hpq; exact h0 hpq
    have hm0 : ((X - C a) ^ 2 + C k : ℝ[X]) ≠ 0 := by
      intro h
      have : ((X - C a) ^ 2 + C k : ℝ[X]).natDegree = 2 := by compute_degree!
      rw [h] at this; simp at this
    have hmd : ((X - C a) ^ 2 + C k : ℝ[X]).natDegree = 2 := by compute_degree!
    have hqd : q.natDegree ≤ 2 * n := by
      have := natDegree_mul hm0 hq0
      rw [← hpq, hmd] at this
      omega
    obtain ⟨r, s, hr, hs, hrs⟩ := ih q hq hqd
    obtain ⟨r', s', h1, h2, h3⟩ := step_mul a k hk n q ⟨r, s, hr, hs, hrs⟩
    exact ⟨r', s', by omega, by omega, by rw [hpq]; exact h3⟩

end RQCMoments

theorem solution (p : Polynomial ℝ) (hp : ∀ t : ℝ, 0 ≤ p.eval t) (d : ℕ)
    (hdeg : p.natDegree = 2 * d) :
    ∃ r s : Polynomial ℝ, r.natDegree ≤ d ∧ s.natDegree ≤ d ∧ p = r ^ 2 + s ^ 2 :=
  RQCMoments.main d p hp hdeg.le
