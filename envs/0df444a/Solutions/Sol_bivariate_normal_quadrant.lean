-- Prove2me | solution 1 for bivariate_normal_quadrant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T19:49:15.81999+00:00
-- url     : https://prove2.me/submissions/aa5d8328-9944-4c27-87f4-a7e47c7523da

import Mathlib

open MeasureTheory Set Real Filter
open scoped Topology

/-! ## Auxiliary one-variable integrals -/

private lemma integral_Ioi_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0:ℝ), Real.exp (-(b * x)) = 1 / b := by
  have h := integral_comp_mul_left_Ioi (fun y : ℝ => Real.exp (-y)) (0:ℝ) hb
  rw [h, mul_zero, integral_exp_neg_Ioi, neg_zero, Real.exp_zero, smul_eq_mul, mul_one,
    one_div]

private lemma integral_Ioi_mul_exp_neg_mul_sq {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2)) = 1 / (2 * a) := by
  have hA1 := integral_Ioi_exp_neg_mul ha
  have h := integral_comp_rpow_Ioi (fun y : ℝ => Real.exp (-(a * y))) (p := 2) (by norm_num)
  rw [hA1] at h
  have key : ∫ x in Ioi (0:ℝ), (2 * (x * Real.exp (-(a * x ^ 2)))) = 1 / a := by
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have h1 : (2:ℝ) - 1 = 1 := by norm_num
    simp only [h1, Real.rpow_one, Real.rpow_two, smul_eq_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  have key2 : 2 * (∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2))) = 1 / a := by
    rw [← integral_const_mul]
    exact key
  have hstep : (∫ x in Ioi (0:ℝ), x * Real.exp (-(a * x ^ 2))) = (1 / a) / 2 := by
    rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0)]
    linarith
  rw [hstep]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

/-! ## The arctan-type integral `∫_0^∞ du / ((u-t)^2+s^2)` -/

private lemma arctan_data {t s : ℝ} (hs : 0 < s) :
    (∀ u ∈ Ioi (0:ℝ),
        HasDerivAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s))
          (((u - t) ^ 2 + s ^ 2)⁻¹) u) ∧
    ContinuousWithinAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) (Ici 0) 0 ∧
    (∀ u ∈ Ioi (0:ℝ), 0 ≤ ((u - t) ^ 2 + s ^ 2)⁻¹) ∧
    Tendsto (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) atTop (𝓝 ((1/s) * (π/2))) := by
  have hderiv : ∀ u ∈ Ioi (0:ℝ),
      HasDerivAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s))
        (((u - t) ^ 2 + s ^ 2)⁻¹) u := by
    intro u _
    have hid : HasDerivAt (fun u : ℝ => u - t) 1 u := by
      simpa using (hasDerivAt_id u).sub_const t
    have h1 : HasDerivAt (fun u : ℝ => (u - t) / s) (1 / s) u := by
      simpa using hid.div_const s
    have h3 := HasDerivAt.arctan (f := fun u : ℝ => (u - t) / s) (x := u) (f' := 1 / s) h1
    have h4 := h3.const_mul (1 / s)
    refine h4.congr_deriv ?_
    have hne : ((u - t) ^ 2 + s ^ 2) ≠ 0 := by positivity
    field_simp
    ring
  have hcont : ContinuousWithinAt (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) (Ici 0) 0 := by
    apply Continuous.continuousWithinAt; fun_prop
  have hpos : ∀ u ∈ Ioi (0:ℝ), 0 ≤ ((u - t) ^ 2 + s ^ 2)⁻¹ := by
    intro u _; positivity
  have hlim : Tendsto (fun u : ℝ => (1 / s) * Real.arctan ((u - t) / s)) atTop
      (𝓝 ((1/s) * (π/2))) := by
    have h1 : Tendsto (fun u : ℝ => u - t) atTop atTop :=
      tendsto_atTop_add_const_right atTop (-t) (tendsto_id (α := ℝ))
    have h2 : Tendsto (fun u : ℝ => (u - t) / s) atTop atTop := h1.atTop_div_const hs
    have h3 : Tendsto (fun u : ℝ => Real.arctan ((u - t) / s)) atTop (𝓝 (π/2)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp h2
    exact h3.const_mul (1/s)
  exact ⟨hderiv, hcont, hpos, hlim⟩

private lemma integral_Ioi_inv_sq_add {t s : ℝ} (hs : 0 < s) :
    ∫ u in Ioi (0:ℝ), ((u - t) ^ 2 + s ^ 2)⁻¹ = (π / 2 + Real.arctan (t / s)) / s := by
  obtain ⟨hderiv, hcont, hpos, hlim⟩ := arctan_data (t := t) hs
  have hmain := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim
  rw [hmain]
  simp only [zero_sub, neg_div, arctan_neg]
  have hs' : s ≠ 0 := hs.ne'
  field_simp
  ring

private lemma integrableOn_Ioi_inv_sq_add {t s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ => ((u - t) ^ 2 + s ^ 2)⁻¹) (Ioi 0) := by
  obtain ⟨hderiv, hcont, hpos, hlim⟩ := arctan_data (t := t) hs
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim

/-! ## The bivariate normal quadrant formula -/

theorem bivariate_normal_quadrant (t : ℝ) (ht1 : -1 < t) (ht2 : t < 1) :
    ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (1 / (2 * Real.pi * Real.sqrt (1 - t ^ 2))) *
          Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2)))
      = 1 / 4 + Real.arcsin t / (2 * Real.pi) := by
  have hS : (0:ℝ) < 1 - t ^ 2 := by
    nlinarith [mul_pos (by linarith : (0:ℝ) < 1 + t) (by linarith : (0:ℝ) < 1 - t)]
  set s : ℝ := Real.sqrt (1 - t ^ 2) with hsdef
  have hs : (0:ℝ) < s := by rw [hsdef]; exact Real.sqrt_pos.2 hS
  have hs2 : s ^ 2 = 1 - t ^ 2 := by rw [hsdef]; exact Real.sq_sqrt hS.le
  set c : ℝ := 1 / (2 * Real.pi * s) with hc
  have hcpos : (0:ℝ) < c := by rw [hc]; positivity
  set A : ℝ → ℝ := fun u => 1 - 2 * t * u + u ^ 2 with hA
  have hAeq : ∀ u : ℝ, A u = (u - t) ^ 2 + (1 - t ^ 2) := by intro u; rw [hA]; ring
  have hApos : ∀ u : ℝ, 0 < A u := by
    intro u; rw [hAeq u]; nlinarith [sq_nonneg (u - t), hS]
  set G : ℝ → ℝ → ℝ :=
    fun x u => c * (x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2)))) with hG
  -- STEP 1: dilation `y = x * u` in the inner integral
  have hstep1 : ∀ x ∈ Ioi (0:ℝ),
      (∫ y in Ioi (0:ℝ),
        c * Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2))))
      = ∫ u in Ioi (0:ℝ),
          x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) /
            (2 * (1 - t ^ 2)))) := by
    intro x hx
    have hx0 : 0 < x := hx
    have h := integral_comp_mul_left_Ioi
      (fun y : ℝ => c * Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2))))
      (0:ℝ) hx0
    simp only [mul_zero] at h
    rw [show (∫ u in Ioi (0:ℝ), x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) / (2 * (1 - t ^ 2)))))
        = x * ∫ u in Ioi (0:ℝ), (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) / (2 * (1 - t ^ 2)))) from integral_const_mul x _]
    rw [h]
    simp only [smul_eq_mul]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hstep1]
  -- STEP 2: identify the integrand with `G`
  have hstep2 : ∀ x ∈ Ioi (0:ℝ),
      (∫ u in Ioi (0:ℝ),
          x * (c * Real.exp (-(x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2) /
            (2 * (1 - t ^ 2)))))
      = ∫ u in Ioi (0:ℝ), G x u := by
    intro x _
    refine setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    have hexp : x ^ 2 - 2 * t * x * (x * u) + (x * u) ^ 2 = x ^ 2 * A u := by
      rw [hA]; ring
    simp only [hG, hexp]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hstep2]
  -- STEP 3: evaluate the inner `x`-integral for fixed `u`
  have hInner : ∀ u ∈ Ioi (0:ℝ), (∫ x in Ioi (0:ℝ), G x u)
      = c * (1 - t ^ 2) * ((u - t) ^ 2 + (1 - t ^ 2))⁻¹ := by
    intro u _
    have hApos' : 0 < A u / (2 * (1 - t ^ 2)) := div_pos (hApos u) (by linarith)
    have h1 : ∫ x in Ioi (0:ℝ), x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2))
        = 1 / (2 * (A u / (2 * (1 - t ^ 2)))) := integral_Ioi_mul_exp_neg_mul_sq hApos'
    have hsplit : ∫ x in Ioi (0:ℝ), G x u
        = c * ∫ x in Ioi (0:ℝ), x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))) := by
      simp only [hG]
      rw [integral_const_mul]
    have h2 : ∫ x in Ioi (0:ℝ), G x u
        = c * ∫ x in Ioi (0:ℝ), x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2)) := by
      rw [hsplit]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      have h3 : -(x ^ 2 * A u) / (2 * (1 - t ^ 2))
          = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by
        field_simp
      rw [h3]
    rw [h2, h1, hAeq u]
    have hne : ((u - t) ^ 2 + (1 - t ^ 2)) ≠ 0 := by nlinarith [sq_nonneg (u - t), hS]
    have hS' : (1 - t ^ 2) ≠ 0 := hS.ne'
    field_simp
  -- STEP 4: Tonelli
  have hmeas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    simp only [hG, hA]
    fun_prop
  have hInt : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards with u
      have ha : 0 < A u / (2 * (1 - t ^ 2)) := div_pos (hApos u) (by linarith)
      have h1c : Integrable
          (fun x : ℝ => x * Real.exp (-(A u / (2 * (1 - t ^ 2))) * x ^ 2)) :=
        integrable_mul_exp_neg_mul_sq ha
      have h1 : Integrable
          (fun x : ℝ => x * Real.exp (-(A u / (2 * (1 - t ^ 2)) * x ^ 2))) := by
        refine Integrable.congr h1c ?_
        filter_upwards with x
        have h4 : -(A u / (2 * (1 - t ^ 2))) * x ^ 2
            = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by ring
        rw [h4]
      have h2 : Integrable
          (fun x : ℝ => c * (x * Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))))) := by
        refine Integrable.congr (h1.const_mul c) ?_
        filter_upwards with x
        have h3 : -(x ^ 2 * A u) / (2 * (1 - t ^ 2))
            = -(A u / (2 * (1 - t ^ 2)) * x ^ 2) := by
          field_simp
        rw [h3]
      exact h2.integrableOn
    · have hbase : IntegrableOn
          (fun u : ℝ => c * (1 - t ^ 2) * ((u - t) ^ 2 + (1 - t ^ 2))⁻¹) (Ioi 0) := by
        have h := (integrableOn_Ioi_inv_sq_add (t := t) (s := s) hs).const_mul (c * (1 - t ^ 2))
        rw [hs2] at h
        exact h
      refine Integrable.congr hbase ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hnorm : ∀ x ∈ Ioi (0:ℝ), ‖Function.uncurry G (x,u)‖ = G x u := by
        intro x hx
        have hx0 : 0 < x := hx
        have hpos : 0 < G x u := by
          rw [hG]
          have hexp : 0 < Real.exp (-(x ^ 2 * A u) / (2 * (1 - t ^ 2))) := Real.exp_pos _
          positivity
        simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
        exact abs_of_pos hpos
      rw [setIntegral_congr_fun measurableSet_Ioi hnorm, hInner u hu]
  rw [integral_integral_swap hInt]
  rw [setIntegral_congr_fun measurableSet_Ioi hInner]
  rw [integral_const_mul]
  -- STEP 5: the remaining one-variable integral and the final arithmetic
  have hB := integral_Ioi_inv_sq_add (t := t) (s := s) hs
  have harc : Real.arctan (t / s) = Real.arcsin t := by
    rw [hsdef]
    exact (Real.arcsin_eq_arctan ⟨ht1, ht2⟩).symm
  rw [← hs2]
  rw [hB, harc]
  rw [hc]
  field_simp
  ring

/-- The quadrant formula, packaged as the platform solution. -/
theorem solution (t : ℝ) (ht1 : -1 < t) (ht2 : t < 1) :
    ∫ x in Set.Ioi (0 : ℝ), ∫ y in Set.Ioi (0 : ℝ),
        (1 / (2 * Real.pi * Real.sqrt (1 - t ^ 2))) *
          Real.exp (-(x ^ 2 - 2 * t * x * y + y ^ 2) / (2 * (1 - t ^ 2)))
      = 1 / 4 + Real.arcsin t / (2 * Real.pi) :=
  bivariate_normal_quadrant t ht1 ht2

#print axioms solution
