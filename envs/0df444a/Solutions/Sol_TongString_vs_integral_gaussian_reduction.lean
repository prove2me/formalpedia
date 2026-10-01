-- Prove2me | solution 1 for TongString.vs_integral_gaussian_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T17:15:39.0329+00:00
-- url     : https://prove2.me/submissions/144f37cb-2140-4029-b9a2-b2e4d54bace6

import Mathlib
import Definitions.Def_TongString_vs_integral

namespace TongString

open Complex MeasureTheory

/-- Gaussian integral over ℂ. -/
lemma bd_gauss (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    ∫ z : ℂ, cexp (-((t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (u : ℂ) * ((‖1 - z‖ ^ 2 : ℝ) : ℂ))) =
      (Real.pi : ℂ) / ((t : ℂ) + u) * cexp (-((t : ℂ) * u / (t + u))) := by
  have hb : 0 < ((t : ℂ) + u).re := by simp; linarith
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (2 * (u : ℂ)) (1 : ℂ)
  have hfin : ((Module.finrank ℝ ℂ : ℂ) / 2) = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfin, cpow_one] at key
  have hpt : ∀ z : ℂ, -((t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (u : ℂ) * ((‖1 - z‖ ^ 2 : ℝ) : ℂ)) =
      (-((t : ℂ) + u) * ((‖z‖ : ℂ)) ^ 2 + 2 * (u : ℂ) * ((inner ℝ (1 : ℂ) z : ℝ) : ℂ)) + (-(u : ℂ)) := by
    intro z
    have h1 : ‖1 - z‖ ^ 2 = ‖(1 : ℂ)‖ ^ 2 - 2 * inner ℝ (1 : ℂ) z + ‖z‖ ^ 2 := norm_sub_sq_real _ _
    rw [h1]; simp; ring
  have hpt2 : ∀ z : ℂ, cexp (-((t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (u : ℂ) * ((‖1 - z‖ ^ 2 : ℝ) : ℂ))) =
      cexp (-((t : ℂ) + u) * ((‖z‖ : ℂ)) ^ 2 + 2 * (u : ℂ) * ((inner ℝ (1 : ℂ) z : ℝ) : ℂ)) *
        cexp (-(u : ℂ)) := fun z => by rw [hpt, Complex.exp_add]
  simp_rw [hpt2]
  rw [integral_mul_const, key]
  have htu : (t : ℂ) + u ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  simp
  field_simp
  ring

/-- Gamma representation. -/
lemma bd_gammarep (a : ℂ) (ha : a.re < 1) (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), (t : ℂ) ^ (-a) * cexp (-((t : ℂ) * ((x ^ 2 : ℝ) : ℂ))) =
      Gamma (1 - a) * (x : ℂ) ^ (2 * a - 2) := by
  have h1 : 0 < (1 - a).re := by simp; linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have key := integral_cpow_mul_exp_neg_mul_Ioi h1 hx2
  have e1 : (1 - a) - 1 = -a := by ring
  rw [e1] at key
  have : ∀ t : ℝ, (t : ℂ) ^ (-a) * cexp (-((t : ℂ) * ((x ^ 2 : ℝ) : ℂ))) =
      (t : ℂ) ^ (-a) * cexp (-(((x ^ 2 : ℝ) : ℂ) * t)) := by
    intro t; rw [mul_comm (t : ℂ)]
  simp_rw [this]
  rw [key, mul_comm]
  congr 1
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hx20 : ((1 / x ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (1 / x ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hcast : ((1 : ℂ) / ((x ^ 2 : ℝ) : ℂ)) = ((1 / x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, cpow_def_of_ne_zero hx20, cpow_def_of_ne_zero hx0,
    ← ofReal_log (by positivity), ← ofReal_log hx.le]
  congr 1
  rw [Real.log_div (by norm_num) hx2.ne', Real.log_one, Real.log_pow]
  push_cast; ring

lemma bd_ball_int (p : ℝ) (hp : p < 2) :
    Integrable ((Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => ‖z‖ ^ (-p))) := by
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  refine integrableOn_ball_of_norm_le_rpow (μ := (volume : Measure ℂ)) (C := 1) (α := p)
    (by rw [Complex.finrank_real_complex]; norm_num)
    (by rw [Complex.finrank_real_complex]; exact_mod_cast hp) ?_ ?_
  · filter_upwards with z
    simp [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  · exact (by fun_prop : Measurable (fun z : ℂ => ‖z‖ ^ (-p))).aestronglyMeasurable

lemma bd_g_int (p q : ℝ) (_hp0 : 0 ≤ p) (_hq0 : 0 ≤ q) (hp : p < 2) (hq : q < 2) (hpq : 2 < p + q) :
    Integrable (fun z : ℂ => ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q)) := by
  set φp := (Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => ‖z‖ ^ (-p))
  set φq := (Metric.ball (0 : ℂ) 1).indicator (fun z : ℂ => ‖z‖ ^ (-q))
  have i1 : Integrable φp := bd_ball_int p hp
  have i2 : Integrable (fun z : ℂ => φq (1 - z)) := (bd_ball_int q hq).comp_sub_left 1
  have i3 : Integrable (fun z : ℂ => (1 + ‖z‖) ^ (-(p + q))) :=
    integrable_one_add_norm (by rw [Complex.finrank_real_complex]; exact_mod_cast hpq)
  set C3 : ℝ := 1 / ((3 : ℝ) ^ (-p) * (5 : ℝ) ^ (-q))
  refine Integrable.mono' (((i1.const_mul (2 ^ q)).add (i2.const_mul (2 ^ p))).add
    (i3.const_mul C3)) ?_ ?_
  · exact (by fun_prop : Measurable (fun z : ℂ => ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q))).aestronglyMeasurable
  · filter_upwards with z
    have hA : 0 ≤ ‖z‖ ^ (-p) := Real.rpow_nonneg (norm_nonneg _) _
    have hB : 0 ≤ ‖1 - z‖ ^ (-q) := Real.rpow_nonneg (norm_nonneg _) _
    have hφp : 0 ≤ φp z := Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have hφq : 0 ≤ φq (1 - z) :=
      Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
    have h3 : 0 ≤ C3 * (1 + ‖z‖) ^ (-(p + q)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA hB)]
    simp only [Pi.add_apply]
    by_cases hz : ‖z‖ < 1 / 2
    · have h1z : 1 / 2 ≤ ‖1 - z‖ := by
        have := norm_sub_norm_le (1 : ℂ) z; simp at this; linarith
      have hBle : ‖1 - z‖ ^ (-q) ≤ 2 ^ q := by
        calc ‖1 - z‖ ^ (-q) ≤ (1 / 2 : ℝ) ^ (-q) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) h1z (by linarith)
          _ = 2 ^ q := by rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      have hφ : φp z = ‖z‖ ^ (-p) := by
        simp only [φp]; rw [Set.indicator_of_mem (by simp; linarith)]
      have : ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q) ≤ 2 ^ q * φp z := by
        rw [hφ, mul_comm (2 ^ q)]; exact mul_le_mul_of_nonneg_left hBle hA
      have : 0 ≤ 2 ^ p * φq (1 - z) := by positivity
      linarith
    by_cases hz1 : ‖1 - z‖ < 1 / 2
    · have h1z : 1 / 2 ≤ ‖z‖ := by
        have := norm_sub_norm_le (1 : ℂ) (1 - z); simp at this; linarith
      have hAle : ‖z‖ ^ (-p) ≤ 2 ^ p := by
        calc ‖z‖ ^ (-p) ≤ (1 / 2 : ℝ) ^ (-p) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) h1z (by linarith)
          _ = 2 ^ p := by rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      have hφ : φq (1 - z) = ‖1 - z‖ ^ (-q) := by
        simp only [φq]; rw [Set.indicator_of_mem (by simp; linarith)]
      have : ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q) ≤ 2 ^ p * φq (1 - z) := by
        rw [hφ]; exact mul_le_mul_of_nonneg_right hAle hB
      have : 0 ≤ 2 ^ q * φp z := by positivity
      linarith
    · push Not at hz hz1
      have hx : 0 < 1 + ‖z‖ := by positivity
      have hA' : ‖z‖ ^ (-p) ≤ ((1 + ‖z‖) / 3) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      have hB' : ‖1 - z‖ ^ (-q) ≤ ((1 + ‖z‖) / 5) ^ (-q) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
        have := norm_sub_norm_le z (z - 1)
        have e : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev _ _
        simp at this; linarith
      have hprod : ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q) ≤ C3 * (1 + ‖z‖) ^ (-(p + q)) := by
        calc ‖z‖ ^ (-p) * ‖1 - z‖ ^ (-q) ≤ ((1 + ‖z‖) / 3) ^ (-p) * ((1 + ‖z‖) / 5) ^ (-q) :=
              mul_le_mul hA' hB' hB (by positivity)
          _ = C3 * (1 + ‖z‖) ^ (-(p + q)) := by
              rw [Real.div_rpow hx.le (by norm_num), Real.div_rpow hx.le (by norm_num),
                neg_add, Real.rpow_add hx]
              simp only [C3]
              field_simp
      have : 0 ≤ 2 ^ q * φp z := by positivity
      have : 0 ≤ 2 ^ p * φq (1 - z) := by positivity
      linarith


lemma bd_gammarep_re (α : ℝ) (hα : α < 1) (x : ℝ) (hx : 0 < x) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-α) * Real.exp (-(t * x ^ 2)) =
      Real.Gamma (1 - α) * x ^ (2 * α - 2) := by
  have h1 : 0 < 1 - α := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi h1 hx2
  have e1 : (1 - α) - 1 = -α := by ring
  rw [e1] at key
  have : ∀ t : ℝ, t ^ (-α) * Real.exp (-(t * x ^ 2)) = t ^ (-α) * Real.exp (-(x ^ 2 * t)) := by
    intro t; rw [mul_comm t]
  simp_rw [this]
  rw [key, mul_comm]
  congr 1
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hx]
  congr 1
  rw [Real.log_div (by norm_num) hx2.ne', Real.log_one, Real.log_pow]
  push_cast; ring

lemma bd_normA (a : ℂ) (x t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (-a) * cexp (-((t : ℂ) * ((x ^ 2 : ℝ) : ℂ)))‖ =
      t ^ (-a.re) * Real.exp (-(t * x ^ 2)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  congr 2
  rw [Complex.neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]

end TongString

open TongString Complex MeasureTheory in
theorem solution (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : (a + b).re < 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi / (Gamma (1 - a) * Gamma (1 - b)) *
        ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
          (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) *
            Complex.exp (-((t : ℂ) * u / (t + u))) := by
  have hab' : a.re + b.re < 1 := by simpa using hab
  have ha1 : a.re < 1 := by linarith
  have hb1 : b.re < 1 := by linarith
  set μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hμ
  set A : ℂ → ℝ → ℂ := fun z t => (t : ℂ) ^ (-a) * cexp (-((t : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ)))
    with hA
  set B : ℂ → ℝ → ℂ := fun z u => (u : ℂ) ^ (-b) * cexp (-((u : ℂ) * ((‖1 - z‖ ^ 2 : ℝ) : ℂ)))
    with hB
  set F : ℝ × ℝ → ℂ → ℂ := fun p z => A z p.1 * B z p.2 with hF
  set G : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) ^ (-a) * (p.2 : ℂ) ^ (-b) / ((p.1 : ℂ) + p.2) *
      Complex.exp (-((p.1 : ℂ) * p.2 / (p.1 + p.2))) with hG
  have hGa : Gamma (1 - a) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hGb : Gamma (1 - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)
  have h1 : ∀ᵐ z : ℂ, z ≠ 1 := compl_mem_ae_iff.mpr (measure_singleton 1)
  have hpos : ∀ᵐ p ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 := by
    rw [hμ, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact hp
  -- integrals of A and B
  have intA : ∀ z : ℂ, z ≠ 0 → ∫ t, A z t ∂μ = Gamma (1 - a) * (‖z‖ : ℂ) ^ (2 * a - 2) := by
    intro z hz
    exact bd_gammarep a ha1 ‖z‖ (norm_pos_iff.mpr hz)
  have intB : ∀ z : ℂ, z ≠ 1 → ∫ u, B z u ∂μ = Gamma (1 - b) * (‖1 - z‖ : ℂ) ^ (2 * b - 2) := by
    intro z hz
    exact bd_gammarep b hb1 ‖1 - z‖ (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz)))
  have cpow_ne : ∀ (x : ℝ) (s : ℂ), 0 < x → (x : ℂ) ^ s ≠ 0 := by
    intro x s hx
    rw [← norm_pos_iff, norm_cpow_eq_rpow_re_of_pos hx]; positivity
  have iA : ∀ z : ℂ, z ≠ 0 → Integrable (A z) μ := by
    intro z hz
    apply Integrable.of_integral_ne_zero
    rw [intA z hz]
    exact mul_ne_zero hGa (cpow_ne _ _ (norm_pos_iff.mpr hz))
  have iB : ∀ z : ℂ, z ≠ 1 → Integrable (B z) μ := by
    intro z hz
    apply Integrable.of_integral_ne_zero
    rw [intB z hz]
    exact mul_ne_zero hGb (cpow_ne _ _ (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz))))
  -- norm integrals
  have nA : ∀ z : ℂ, z ≠ 0 → ∫ t, ‖A z t‖ ∂μ = Real.Gamma (1 - a.re) * ‖z‖ ^ (2 * a.re - 2) := by
    intro z hz
    rw [← bd_gammarep_re a.re ha1 ‖z‖ (norm_pos_iff.mpr hz)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact bd_normA a ‖z‖ t ht
  have nB : ∀ z : ℂ, z ≠ 1 →
      ∫ u, ‖B z u‖ ∂μ = Real.Gamma (1 - b.re) * ‖1 - z‖ ^ (2 * b.re - 2) := by
    intro z hz
    rw [← bd_gammarep_re b.re hb1 ‖1 - z‖ (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz)))]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    exact bd_normA b ‖1 - z‖ t ht
  -- measurability
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((μ.prod μ).prod volume) := by
    apply Measurable.aestronglyMeasurable
    simp only [hF, hA, hB]
    fun_prop
  -- joint integrability
  have hH : Integrable (Function.uncurry F) ((μ.prod μ).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · filter_upwards [h0, h1] with z hz0 hz1
      exact (iA z hz0).mul_prod (iB z hz1)
    · have hg := (bd_g_int (2 - 2 * a.re) (2 - 2 * b.re) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)).const_mul
          (Real.Gamma (1 - a.re) * Real.Gamma (1 - b.re))
      refine hg.congr ?_
      filter_upwards [h0, h1] with z hz0 hz1
      simp only [Function.uncurry, hF, norm_mul]
      rw [integral_prod_mul (fun t => ‖A z t‖) (fun u => ‖B z u‖), nA z hz0, nB z hz1]
      rw [show -(2 - 2 * a.re) = 2 * a.re - 2 by ring, show -(2 - 2 * b.re) = 2 * b.re - 2 by ring]
      ring
  -- inner Gaussian integral
  have hinner : ∀ᵐ p ∂(μ.prod μ), ∫ z, F p z = (Real.pi : ℂ) * G p := by
    filter_upwards [hpos] with p hp
    have e : ∀ z : ℂ, F p z = (p.1 : ℂ) ^ (-a) * (p.2 : ℂ) ^ (-b) *
        cexp (-((p.1 : ℂ) * ((‖z‖ ^ 2 : ℝ) : ℂ) + (p.2 : ℂ) * ((‖1 - z‖ ^ 2 : ℝ) : ℂ))) := by
      intro z
      simp only [hF, hA, hB]
      rw [neg_add, Complex.exp_add]; ring
    simp_rw [e]
    rw [integral_const_mul, bd_gauss p.1 p.2 hp.1 hp.2]
    simp only [hG]
    ring
  have hGint : Integrable G (μ.prod μ) := by
    have h2 : Integrable (fun p => (Real.pi : ℂ) * G p) (μ.prod μ) :=
      hH.integral_prod_left.congr hinner
    have h3 := h2.const_mul ((Real.pi : ℂ)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall fun p => ?_)
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only
    field_simp
  -- pointwise representation of the integrand
  have hrep : ∀ᵐ z : ℂ, ((‖z‖ : ℂ) ^ (2 * a - 2)) * ((‖1 - z‖ : ℂ) ^ (2 * b - 2)) =
      (∫ p, F p z ∂(μ.prod μ)) / (Gamma (1 - a) * Gamma (1 - b)) := by
    filter_upwards [h0, h1] with z hz0 hz1
    simp only [hF]
    rw [integral_prod_mul (A z) (B z), intA z hz0, intB z hz1]
    field_simp
  unfold virasoroShapiroIntegral
  rw [integral_congr_ae hrep, integral_div, ← integral_integral_swap hH,
    integral_congr_ae hinner, integral_const_mul, integral_prod G hGint]
  simp only [hG, hμ]
  field_simp
