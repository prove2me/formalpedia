-- Prove2me | solution 1 for RandomListsMatching.GeneralRates.claim3_g_monotone_first_arg
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T00:03:44.330182+00:00
-- url     : https://prove2.me/submissions/3ce6909f-a6bc-4e0d-a441-92a1f508de91

import Mathlib
import Definitions.Def_RandomListsMatching_GeneralRates_Setting

open RandomListsMatching.GeneralRates

noncomputable def RLMx_E (u : ℝ) : ℝ := ∫ t in (0:ℝ)..1, Real.exp (u * t)

lemma RLMx_E_zero : RLMx_E 0 = 1 := by simp [RLMx_E]

lemma RLMx_E_closed {u : ℝ} (hu : u ≠ 0) : RLMx_E u = (Real.exp u - 1) / u := by
  unfold RLMx_E
  rw [intervalIntegral.integral_comp_mul_left Real.exp hu, integral_exp]
  simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul]
  ring

lemma RLMx_E_cont (u : ℝ) : Continuous (fun t : ℝ => Real.exp (u * t)) := by fun_prop

lemma RLMx_E_mono : Monotone RLMx_E := by
  intro u v huv
  unfold RLMx_E
  apply intervalIntegral.integral_mono_on (by norm_num) ((RLMx_E_cont u).intervalIntegrable _ _)
    ((RLMx_E_cont v).intervalIntegrable _ _)
  intro t ht
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right huv ht.1)

lemma RLMx_E_convex : ConvexOn ℝ Set.univ RLMx_E := by
  refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold RLMx_E
  have hf : IntervalIntegrable (fun t : ℝ => a * Real.exp (u * t)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => a * Real.exp (u * t)).intervalIntegrable _ _
  have hg : IntervalIntegrable (fun t : ℝ => b * Real.exp (v * t)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => b * Real.exp (v * t)).intervalIntegrable _ _
  have hsum : (∫ t in (0:ℝ)..1, (a * Real.exp (u * t) + b * Real.exp (v * t))) =
      a * (∫ t in (0:ℝ)..1, Real.exp (u * t)) + b * ∫ t in (0:ℝ)..1, Real.exp (v * t) := by
    rw [intervalIntegral.integral_add hf hg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  rw [← hsum]
  apply intervalIntegral.integral_mono_on (by norm_num) ((RLMx_E_cont _).intervalIntegrable _ _)
    (hf.add hg)
  intro t _
  have := convexOn_exp.2 (Set.mem_univ (u * t)) (Set.mem_univ (v * t)) ha hb hab
  simp only [smul_eq_mul] at this
  rw [show (a * u + b * v) * t = a * (u * t) + b * (v * t) by ring]
  exact this

lemma RLMx_E_mul (u : ℝ) : u * RLMx_E u = Real.exp u - 1 := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [RLMx_E_closed hu]; field_simp

lemma RLMx_E_neg (u : ℝ) : RLMx_E (-u) = Real.exp (-u) * RLMx_E u := by
  by_cases hu : u = 0
  · simp [hu, RLMx_E_zero]
  · apply mul_left_cancel₀ hu
    have hm := RLMx_E_mul (-u)
    have hp := RLMx_E_mul u
    have e : Real.exp (-u) * Real.exp u = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-1) * hm - Real.exp (-u) * hp - e

lemma RLMx_h_eq (y x : ℝ) : h y x = y * Real.exp (-y) * RLMx_E (y - x) := by
  unfold h
  split_ifs with hxy
  · subst hxy; simp [RLMx_E_zero]
  · have hne : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
    rw [RLMx_E_closed hne]
    have e1 : Real.exp (y - x) * Real.exp (-y) = Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← e1]
    ring

lemma RLMx_g_eq (y x : ℝ) : g y x = 1 - Real.exp (-x) - x * Real.exp (-x) * RLMx_E (x - y) := by
  unfold g
  rw [RLMx_h_eq, RLMx_h_eq, sub_zero]
  have hA := RLMx_E_mul y
  have hB := RLMx_E_mul (y - x)
  have hR : RLMx_E (x - y) = Real.exp (x - y) * RLMx_E (y - x) := by
    rw [show x - y = -(y - x) by ring, RLMx_E_neg]
  have e1 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
  have e2 : Real.exp (-y) * Real.exp (y - x) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-x) * Real.exp (x - y) = Real.exp (-y) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination Real.exp (-y) * hA - Real.exp (-y) * hB + x * Real.exp (-x) * hR + e1 - e2 +
    x * RLMx_E (y - x) * e3

lemma RLMx_h_convex {y : ℝ} (hy : 0 ≤ y) : ConvexOn ℝ Set.univ (h y) := by
  refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
  simp only [smul_eq_mul]
  rw [RLMx_h_eq, RLMx_h_eq, RLMx_h_eq]
  have hc : 0 ≤ y * Real.exp (-y) := by positivity
  have := RLMx_E_convex.2 (Set.mem_univ (y - a)) (Set.mem_univ (y - b)) hs ht hst
  simp only [smul_eq_mul] at this
  rw [show y - (s * a + t * b) = s * (y - a) + t * (y - b) by linear_combination (-y) * hst]
  have := mul_le_mul_of_nonneg_left this hc
  linarith

lemma RLMx_h_anti (y : ℝ) (hy : 0 ≤ y) {a b : ℝ} (hab : a ≤ b) : h y b ≤ h y a := by
  rw [RLMx_h_eq, RLMx_h_eq]
  exact mul_le_mul_of_nonneg_left (RLMx_E_mono (by linarith)) (by positivity)

lemma RLMx_hasDeriv {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => h y t) ((1 - Real.exp (-y)) / y - 1) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-0) * (-1)) 0 := (hasDerivAt_neg 0).exp
  have h2 : HasDerivAt (fun t : ℝ => y - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub y
  have h3 := h2.inv (by simp [hy.ne'])
  have h4 := ((h1.sub_const (Real.exp (-y))).const_mul y).mul h3
  have heq : (fun t => h y t) =ᶠ[nhds 0]
      (fun t => y * (Real.exp (-t) - Real.exp (-y)) * (y - t)⁻¹) := by
    filter_upwards [eventually_ne_nhds (show (0:ℝ) ≠ y from hy.ne)] with t ht
    unfold h
    rw [if_neg ht]; ring
  refine (h4.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [neg_zero, Real.exp_zero, sub_zero, Pi.inv_apply]
  field_simp
  ring

lemma RLMx_eq5 (y x : ℝ) (hx0 : 0 ≤ x) (hxy : x ≤ y) (hy1 : y ≤ 1) :
    h y 0 - h y x ≤ -x * deriv (fun t => h y t) 0 ∧
      -x * deriv (fun t => h y t) 0 ≤ Real.exp (-1) * x := by
  rcases hx0.lt_or_eq with hxp | hx0'
  swap
  · subst hx0'; simp
  have hy : 0 < y := lt_of_lt_of_le hxp hxy
  have hd := RLMx_hasDeriv hy
  rw [hd.deriv]
  constructor
  · have hs := (RLMx_h_convex hy.le).le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ x) hxp hd
    rw [slope_def_field, sub_zero, le_div_iff₀ hxp] at hs
    linarith
  · have hF : (1 - Real.exp (-y)) / y = RLMx_E (-y) := by
      rw [RLMx_E_closed (neg_ne_zero.2 hy.ne'), div_neg, ← neg_div, neg_sub]
    have hF1 : RLMx_E (-1) = 1 - Real.exp (-1) := by rw [RLMx_E_closed (by norm_num)]; ring
    have hmono := RLMx_E_mono (show (-1:ℝ) ≤ -y by linarith)
    rw [hF]
    nlinarith [mul_le_mul_of_nonneg_left hmono hx0]

lemma RLMx_g_mono_y {x y z : ℝ} (hx : 0 ≤ x) (hyz : y ≤ z) : g y x ≤ g z x := by
  rw [RLMx_g_eq, RLMx_g_eq]
  have hxe : 0 ≤ x * Real.exp (-x) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (RLMx_E_mono (by linarith : x - z ≤ x - y)) hxe]

theorem solution (x : ℝ) (hx0 : 0 ≤ x) :
    MonotoneOn (fun y => g y x) (Set.Ici x) := by
  intro a _ b _ hab
  exact RLMx_g_mono_y hx0 hab
