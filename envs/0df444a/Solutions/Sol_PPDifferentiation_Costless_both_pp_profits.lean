-- Prove2me | solution 1 for PPDifferentiation.Costless.both_pp_profits
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T18:50:33.648662+00:00
-- url     : https://prove2.me/submissions/5172503f-573e-4203-b01a-1b1f91757c98

import Mathlib
import Definitions.Def_PPDifferentiation_Costless_Setting

set_option autoImplicit false
open MeasureTheory PPDifferentiation.Costless

lemma ppd_ramp_dec (k m : ℝ) (hk : 0 ≤ k) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    ∫ x in (0:ℝ)..1, max 0 (k * (m - x)) = k * m ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max 0 (k * (m - x)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0:ℝ)..m, max 0 (k * (m - x)) = ∫ x in (0:ℝ)..m, k * (m - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only
    exact max_eq_right (mul_nonneg hk (by linarith [hx.2]))
  have e2 : ∫ x in m..1, max 0 (k * (m - x)) = ∫ x in m..1, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk (by linarith [hx.1]))
  rw [e1, e2]
  have : ∫ x in (0:ℝ)..m, k * (m - x) = k * m ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => k * (m * x - x ^ 2 / 2))
      (f' := fun x => k * (m - x))]
    · ring
    · intro x _
      have := (((hasDerivAt_id x).const_mul m).sub ((hasDerivAt_pow 2 x).div_const 2)).const_mul k
      exact this.congr_deriv (by simp)
    · exact (by fun_prop : Continuous fun x : ℝ => k * (m - x)).intervalIntegrable _ _
  rw [this]; simp

lemma ppd_ramp_inc (k m : ℝ) (hk : 0 ≤ k) (h0 : 0 ≤ m) (h1 : m ≤ 1) :
    ∫ x in (0:ℝ)..1, max 0 (k * (x - m)) = k * (1 - m) ^ 2 / 2 := by
  have hc : Continuous fun x : ℝ => max 0 (k * (x - m)) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := m)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have e1 : ∫ x in (0:ℝ)..m, max 0 (k * (x - m)) = ∫ x in (0:ℝ)..m, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h0] at hx
    simp only
    exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hk (by linarith [hx.2]))
  have e2 : ∫ x in m..1, max 0 (k * (x - m)) = ∫ x in m..1, k * (x - m) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h1] at hx
    simp only
    exact max_eq_right (mul_nonneg hk (by linarith [hx.1]))
  rw [e1, e2]
  have : ∫ x in m..1, k * (x - m) = k * (1 - m) ^ 2 / 2 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x => k * (x ^ 2 / 2 - m * x))
      (f' := fun x => k * (x - m))]
    · ring
    · intro x _
      have := (((hasDerivAt_pow 2 x).div_const 2).sub ((hasDerivAt_id x).const_mul m)).const_mul k
      exact this.congr_deriv (by simp)
    · exact (by fun_prop : Continuous fun x : ℝ => k * (x - m)).intervalIntegrable _ _
  rw [this]; simp

lemma ppd_adv_eq (t xi xj x : ℝ) : adv t xi xj x = t * (xi - xj) * (2 * x - xi - xj) := by
  unfold adv; ring

lemma ppd_profPP_left (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xA xB = t * (xB - xA) * (xA + xB)^2 / 4 := by
  have e : ∀ x, adv t xA xB x = (2 * t * (xB - xA)) * ((xA + xB) / 2 - x) := by
    intro x; rw [ppd_adv_eq]; ring
  unfold profPP
  simp_rw [e]
  rw [ppd_ramp_dec _ _ (by nlinarith) (by linarith) (by linarith)]
  ring

lemma ppd_profPP_right (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xB xA = t * (xB - xA) * (2 - xA - xB)^2 / 4 := by
  have e : ∀ x, adv t xB xA x = (2 * t * (xB - xA)) * (x - (xA + xB) / 2) := by
    intro x; rw [ppd_adv_eq]; ring
  unfold profPP
  simp_rw [e]
  rw [ppd_ramp_inc _ _ (by nlinarith) (by linarith) (by linarith)]
  ring

theorem solution (t : ℝ) (ht : 0 < t) (xA xB : ℝ) (hAB : xA ≤ xB)
    (h0 : 0 ≤ xA + xB) (h2 : xA + xB ≤ 2) :
    profPP t xA xB = t * (xB - xA) * (xA + xB)^2 / 4 ∧
    profPP t xB xA = t * (xB - xA) * (2 - xA - xB)^2 / 4 :=
  ⟨ppd_profPP_left t ht xA xB hAB h0 h2, ppd_profPP_right t ht xA xB hAB h0 h2⟩
