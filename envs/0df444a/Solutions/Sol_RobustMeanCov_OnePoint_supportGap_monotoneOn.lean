-- Prove2me | solution 1 for RobustMeanCov.OnePoint.supportGap_monotoneOn
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:13:07.496885+00:00
-- url     : https://prove2.me/submissions/08c53a91-785d-4fbb-bc82-ea8ccfab9dbe

import Mathlib

namespace RobustMeanCov.OnePoint

theorem aux_sgm_repr (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hg : Continuous (deriv u)) (m h : ℝ) (hh : h ≠ 0) :
    (u (m + h) - u m) / h ^ 2 - deriv u m / h
      = ∫ t in (0:ℝ)..1, (deriv u (m + t * h) - deriv u m) / h := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => u (m + t * h) - deriv u m * (t * h))
        (deriv u (m + t * h) * h - deriv u m * h) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => m + t * h) h t := by
      simpa using ((hasDerivAt_id t).mul_const h).const_add m
    have h2 : HasDerivAt u (deriv u (m + t * h)) (m + t * h) :=
      (hu (m + t * h)).hasDerivAt
    have h3 := h2.comp t h1
    have h4 : HasDerivAt (fun t : ℝ => deriv u m * (t * h)) (deriv u m * h) t := by
      simpa using ((hasDerivAt_id t).mul_const h).const_mul (deriv u m)
    exact h3.sub h4
  have hcont : Continuous (fun t : ℝ => deriv u (m + t * h) * h - deriv u m * h) := by
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 1)
  simp only [zero_mul, add_zero, one_mul, mul_zero, sub_zero] at hFTC
  have hpt : (fun t : ℝ => (deriv u (m + t * h) - deriv u m) / h)
      = fun t => (deriv u (m + t * h) * h - deriv u m * h) / h ^ 2 := by
    funext t
    field_simp
  rw [hpt, intervalIntegral.integral_div, hFTC]
  field_simp
  ring

end RobustMeanCov.OnePoint

open RobustMeanCov.OnePoint

theorem solution (u : ℝ → ℝ) (hu : Differentiable ℝ u)
    (hconv : ConvexOn ℝ Set.univ (deriv u)) (m : ℝ) :
    MonotoneOn (fun y : ℝ => (u y - u m) / (y - m) ^ 2 - deriv u m / (y - m)) {y : ℝ | y ≠ m} := by
  have hg : Continuous (deriv u) :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  intro y1 hy1 y2 hy2 hle
  simp only [Set.mem_ofPred_eq] at hy1 hy2
  have e1 : y1 = m + (y1 - m) := by ring
  have e2 : y2 = m + (y2 - m) := by ring
  have h1 : y1 - m ≠ 0 := sub_ne_zero.mpr hy1
  have h2 : y2 - m ≠ 0 := sub_ne_zero.mpr hy2
  show (u y1 - u m) / (y1 - m) ^ 2 - deriv u m / (y1 - m)
      ≤ (u y2 - u m) / (y2 - m) ^ 2 - deriv u m / (y2 - m)
  have r1 := aux_sgm_repr u hu hg m (y1 - m) h1
  have r2 := aux_sgm_repr u hu hg m (y2 - m) h2
  rw [← e1] at r1
  rw [← e2] at r2
  rw [r1, r2]
  apply intervalIntegral.integral_mono_on zero_le_one
  · exact (by fun_prop : Continuous
      (fun t : ℝ => (deriv u (m + t * (y1 - m)) - deriv u m) / (y1 - m))).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous
      (fun t : ℝ => (deriv u (m + t * (y2 - m)) - deriv u m) / (y2 - m))).intervalIntegrable 0 1
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    simp
  have hs := hconv.secant_mono (a := m) (x := m + t * (y1 - m)) (y := m + t * (y2 - m))
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
    (by intro h; apply h1; have : t * (y1 - m) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact h')
    (by intro h; apply h2; have : t * (y2 - m) = 0 := by linarith
        rcases mul_eq_zero.mp this with h' | h'
        · linarith
        · exact h')
    (by nlinarith)
  simp only [add_sub_cancel_left] at hs
  have k1 : (deriv u (m + t * (y1 - m)) - deriv u m) / (y1 - m)
      = t * ((deriv u (m + t * (y1 - m)) - deriv u m) / (t * (y1 - m))) := by
    field_simp
  have k2 : (deriv u (m + t * (y2 - m)) - deriv u m) / (y2 - m)
      = t * ((deriv u (m + t * (y2 - m)) - deriv u m) / (t * (y2 - m))) := by
    field_simp
  rw [k1, k2]
  exact mul_le_mul_of_nonneg_left hs hpos.le
