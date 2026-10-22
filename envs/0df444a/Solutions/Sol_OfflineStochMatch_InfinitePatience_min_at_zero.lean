-- Prove2me | solution 1 for OfflineStochMatch.InfinitePatience.min_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:01:48.698666+00:00
-- url     : https://prove2.me/submissions/d0562ddd-4354-4509-8dad-d3df8a21493e

import Mathlib
import Definitions.Def_OfflineStochMatch_InfinitePatience_Setting
set_option autoImplicit false
open OfflineStochMatch.InfinitePatience

lemma ip_hd (c : ℝ) (x : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (-2 * x)) (Real.exp (-2 * x) * (-2)) x := by
  have h := ((hasDerivAt_id x).const_mul (-2 : ℝ)).exp
  simpa using h

lemma ip_int0 : ∫ x in (0:ℝ)..1, Real.exp (-2 * x) = (1 - Real.exp (-2)) / 2 := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => -(Real.exp (-2 * x)) / 2) (Real.exp (-2 * x)) x := by
    intro x _
    have := ((ip_hd 0 x).neg).div_const 2
    exact this.congr_deriv (by (try simp only [Pi.neg_apply]); ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

lemma ip_int1 : ∫ x in (0:ℝ)..1, x * Real.exp (-2 * x) = 1 / 4 - 3 / 4 * Real.exp (-2) := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => -(Real.exp (-2 * x)) * (x / 2 + 1 / 4))
      (x * Real.exp (-2 * x)) x := by
    intro x _
    have h1 := ((ip_hd 0 x).neg)
    have h2 : HasDerivAt (fun x : ℝ => x / 2 + 1 / 4) (1 / 2) x := by
      simpa using ((hasDerivAt_id x).div_const 2).add_const (1 / 4)
    have := h1.mul h2
    exact this.congr_deriv (by (try simp only [Pi.neg_apply]); ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

lemma ip_int2 : ∫ x in (0:ℝ)..1, x ^ 2 * Real.exp (-2 * x) = 1 / 4 - 5 / 4 * Real.exp (-2) := by
  have h : ∀ x ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun x : ℝ => -(Real.exp (-2 * x)) * (x ^ 2 / 2 + x / 2 + 1 / 4))
      (x ^ 2 * Real.exp (-2 * x)) x := by
    intro x _
    have h1 := ((ip_hd 0 x).neg)
    have h2 : HasDerivAt (fun x : ℝ => x ^ 2 / 2 + x / 2 + 1 / 4) (x + 1 / 2) x := by
      have a1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
      have := ((a1.div_const 2).add ((hasDerivAt_id x).div_const 2)).add_const (1 / 4)
      exact this.congr_deriv (by simp <;> ring)
    have := h1.mul h2
    exact this.congr_deriv (by (try simp only [Pi.neg_apply]); ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h (by apply Continuous.intervalIntegrable; fun_prop)]
  simp
  ring

lemma ip_e2 : 0 < Real.exp (-2) ∧ Real.exp (-2) < 1 / 7 := by
  refine ⟨Real.exp_pos _, ?_⟩
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 : 7 < Real.exp 2 := by rw [h2]; nlinarith
  rw [Real.exp_neg, inv_eq_one_div, div_lt_div_iff₀ (Real.exp_pos 2) (by norm_num)]
  linarith

lemma ip_Ilb (z : ℝ) (hz0 : 0 ≤ z) :
    (1 - Real.exp (-2)) / 2 + 2 * z * (1 / 4 - 3 / 4 * Real.exp (-2)) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * Real.exp (-2))
      ≤ ∫ x in (0:ℝ)..1, Real.exp (-2 * x * (1 - z)) := by
  have hint : ∫ x in (0:ℝ)..1, (Real.exp (-2 * x) + 2 * z * (x * Real.exp (-2 * x)) + 2 * z ^ 2 * (x ^ 2 * Real.exp (-2 * x)))
      = (1 - Real.exp (-2)) / 2 + 2 * z * (1 / 4 - 3 / 4 * Real.exp (-2)) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * Real.exp (-2)) := by
    rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ip_int0, ip_int1, ip_int2]
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  rw [← hint]
  apply intervalIntegral.integral_mono_on zero_le_one
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · intro x hx
    have hx0 := hx.1
    have h1 := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * x * z by positivity)
    have e : Real.exp (-2 * x * (1 - z)) = Real.exp (-2 * x) * Real.exp (2 * x * z) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (-2 * x)).le
    nlinarith [this]

theorem solution (aT : ℝ → ℝ) (haT : aT = expAtt (1 / 2) ∨ aT = linAtt (1 / 2)) :
    IsMinOn (fun z => aT z * ∫ x in (0 : ℝ)..1, Real.exp (-2 * x * (1 - z))) (Set.Icc (0 : ℝ) 1) 0 := by
  intro z hz
  simp only [Set.mem_setOf_eq]
  obtain ⟨hz0, hz1⟩ := hz
  have hlb : 1 - z / 2 ≤ aT z ∧ aT 0 = 1 := by
    rcases haT with h | h
    · subst h
      refine ⟨?_, by simp [expAtt]⟩
      have := Real.add_one_le_exp (-(1 / 2 * z))
      simp only [expAtt]; linarith
    · subst h
      refine ⟨by simp [linAtt]; linarith, by simp [linAtt]⟩
  have hI0 : ∫ x in (0:ℝ)..1, Real.exp (-2 * x * (1 - 0)) = (1 - Real.exp (-2)) / 2 := by
    rw [← ip_int0]; congr 1; ext x; simp
  simp only [hlb.2, hI0, one_mul]
  have hIz := ip_Ilb z hz0
  obtain ⟨he0, he1⟩ := ip_e2
  set e2 := Real.exp (-2)
  set I := ∫ x in (0:ℝ)..1, Real.exp (-2 * x * (1 - z))
  have hP : 0 ≤ (1 - e2) / 2 + 2 * z * (1 / 4 - 3 / 4 * e2) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * e2) := by
    nlinarith [mul_nonneg hz0 hz0]
  have ha : 0 ≤ 1 - z / 2 := by linarith
  have h1 : (1 - z / 2) * ((1 - e2) / 2 + 2 * z * (1 / 4 - 3 / 4 * e2) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * e2)) ≤ aT z * I :=
    mul_le_mul hlb.1 hIz hP (by linarith [hlb.1])
  have h2 : (1 - e2) / 2 ≤ (1 - z / 2) * ((1 - e2) / 2 + 2 * z * (1 / 4 - 3 / 4 * e2) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * e2)) := by
    have hK : 0 ≤ 1 / 4 - 5 / 4 * e2 := by linarith
    have hc : 0 ≤ 1 / 4 - 7 / 4 * e2 := by linarith
    have : (1 - z / 2) * ((1 - e2) / 2 + 2 * z * (1 / 4 - 3 / 4 * e2) + 2 * z ^ 2 * (1 / 4 - 5 / 4 * e2)) - (1 - e2) / 2
        = z * ((1 / 4 - 5 / 4 * e2) * (1 - z ^ 2) + (1 / 4 - 7 / 4 * e2) * z) := by ring
    have h3 : 0 ≤ z * ((1 / 4 - 5 / 4 * e2) * (1 - z ^ 2) + (1 / 4 - 7 / 4 * e2) * z) := by
      apply mul_nonneg hz0
      apply add_nonneg
      · apply mul_nonneg hK; nlinarith
      · exact mul_nonneg hc hz0
    linarith
  linarith
