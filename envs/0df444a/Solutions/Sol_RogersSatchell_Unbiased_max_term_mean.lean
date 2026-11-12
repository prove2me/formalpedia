-- Prove2me | solution 1 for RogersSatchell.Unbiased.max_term_mean
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T21:49:10.76601+00:00
-- url     : https://prove2.me/submissions/7df9a494-9662-408e-9421-2f9017cb563e

import Mathlib
import Definitions.Def_RogersSatchell_Unbiased_Process

set_option autoImplicit false

open MeasureTheory ProbabilityTheory NNReal
open Filter Topology

namespace RSMaxTerm

/-- Gaussian reflection identity (child R2 of the plan): for `Y ~ N(m, v)`, `v ≠ 0`,
`E[f(Y); Y ≤ 0] = E[f(-Y) e^{-(2m/v) Y}; Y ≥ 0]`. -/
lemma gauss_reflect (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ y in Set.Iic 0, f y ∂(gaussianReal m v) =
      ∫⁻ y in Set.Ici 0, f (-y) * ENNReal.ofReal (Real.exp (-(2 * m / v) * y)) ∂(gaussianReal m v) := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  rw [gaussianReal_of_var_ne_zero _ hv,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _) hf measurableSet_Iic,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop)
      measurableSet_Ici]
  rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Ici,
    ← lintegral_neg_eq_self]
  congr 1
  ext y
  by_cases hy : 0 ≤ y
  · have h1 : -y ∈ Set.Iic (0:ℝ) := by simpa using hy
    have h2 : y ∈ Set.Ici (0:ℝ) := hy
    have key : gaussianPDFReal m v (-y) = gaussianPDFReal m v y * Real.exp (-(2 * m / v) * y) := by
      simp only [gaussianPDFReal]
      rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
      congr 2
      field_simp
      ring
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2, Pi.mul_apply, gaussianPDF_def]
    rw [key, ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    ring
  · have h1 : -y ∉ Set.Iic (0:ℝ) := by simp only [Set.mem_Iic]; linarith
    have h2 : y ∉ Set.Ici (0:ℝ) := by simpa using hy
    simp [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- Pointwise layer identity: `s(s-x) = ∫_0^∞ 1{x ≤ a ≤ s} (2a - x) da` for `0 ≤ s`, `x ≤ s`. -/
lemma pw (s x : ℝ) (hs : 0 ≤ s) (hxs : x ≤ s) :
    ENNReal.ofReal (s * (s - x)) = ∫⁻ a in Set.Ioi (0:ℝ),
      Set.indicator {a | a ≤ s ∧ x ≤ a} (fun a => ENNReal.ofReal (2 * a - x)) a := by
  have hset : {a : ℝ | a ≤ s ∧ x ≤ a} = Set.Icc x s := by
    ext a; simp only [Set.mem_setOf_eq, Set.mem_Icc]; exact and_comm
  rw [hset, lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have hd : ∀ a, HasDerivAt (fun a : ℝ => a * a - x * a) (2 * a - x) a := by
    intro a
    exact (((hasDerivAt_id' a).mul (hasDerivAt_id' a)).sub
      ((hasDerivAt_id' a).const_mul x)).congr_deriv (by ring)
  rcases le_or_gt x 0 with hx | hx
  · have hI : Set.Icc x s ∩ Set.Ioi 0 = Set.Ioc 0 s := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
    rw [hI, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le hs,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      ring
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self
    · exact ae_restrict_of_forall_mem measurableSet_Ioc (fun a ha => by
        simp only [Set.mem_Ioc] at ha; simp only [Pi.zero_apply]; linarith [ha.1])
  · have hI : Set.Icc x s ∩ Set.Ioi 0 = Set.Icc x s := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioi]
      constructor
      · rintro ⟨h, _⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, by linarith⟩
    rw [hI, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxs,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ => hd a)
          (by apply Continuous.intervalIntegrable; fun_prop)]
      ring
    · exact Continuous.integrableOn_Icc (by fun_prop)
    · exact ae_restrict_of_forall_mem measurableSet_Icc (fun a ha => by
        simp only [Set.mem_Icc] at ha; simp only [Pi.zero_apply]; linarith [ha.1])

/-- Inner `a`-integral, `κ ≠ 0`. -/
lemma inner_eval_ne (κ x : ℝ) (hκ : κ ≠ 0) :
    ∫⁻ a in Set.Ioi (0:ℝ), Set.indicator (Set.Iic x)
      (fun a => ENNReal.ofReal x * ENNReal.ofReal (Real.exp (κ * (a - x)))) a =
    ENNReal.ofReal (max x 0 * (1 - Real.exp (-κ * max x 0)) / κ) := by
  rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rcases le_or_gt x 0 with hx | hx
  · have : Set.Iic x ∩ Set.Ioi (0:ℝ) = ∅ := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2; linarith
    rw [this, Measure.restrict_empty, lintegral_zero_measure, max_eq_right hx]; simp
  · have hI : Set.Iic x ∩ Set.Ioi (0:ℝ) = Set.Ioc 0 x := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]; exact and_comm
    rw [hI, max_eq_left hx.le]
    have hcongr : ∀ a : ℝ, ENNReal.ofReal x * ENNReal.ofReal (Real.exp (κ * (a - x))) =
        ENNReal.ofReal (x * Real.exp (κ * (a - x))) := fun a => (ENNReal.ofReal_mul hx.le).symm
    simp_rw [hcongr]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le hx.le]
      have hd : ∀ a ∈ Set.uIcc 0 x, HasDerivAt (fun a => x * Real.exp (κ * (a - x)) / κ)
          (x * Real.exp (κ * (a - x))) a := by
        intro a _
        have h1 : HasDerivAt (fun a => κ * (a - x)) κ a := by
          simpa using ((hasDerivAt_id a).sub_const x).const_mul κ
        exact ((h1.exp.const_mul x).div_const κ).congr_deriv (by rw [div_eq_iff hκ]; ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
        (by apply Continuous.intervalIntegrable; fun_prop)]
      rw [show κ * (x - x) = 0 by ring, show κ * (0 - x) = -κ * x by ring, Real.exp_zero]
      ring
    · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ioc_subset_Icc_self
    · exact ae_of_all _ (fun a => by simp only [Pi.zero_apply]; positivity)

/-- Inner `a`-integral, `κ = 0`. -/
lemma inner_eval_zero (x : ℝ) :
    ∫⁻ a in Set.Ioi (0:ℝ), Set.indicator (Set.Iic x)
      (fun a => ENNReal.ofReal x * ENNReal.ofReal (Real.exp (0 * (a - x)))) a =
    ENNReal.ofReal (max x 0 * max x 0) := by
  simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  rcases le_or_gt x 0 with hx | hx
  · have : Set.Iic x ∩ Set.Ioi (0:ℝ) = ∅ := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false,
        iff_false, not_and]
      intro h1 h2; linarith
    rw [this, Measure.restrict_empty, lintegral_zero_measure, max_eq_right hx]; simp
  · have hI : Set.Iic x ∩ Set.Ioi (0:ℝ) = Set.Ioc 0 x := by
      ext a; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_Ioc]; exact and_comm
    rw [hI, max_eq_left hx.le, setLIntegral_const, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul hx.le]

/-- Outer Gaussian computation, `κ ≠ 0`, `κ v = 2 m`. -/
lemma gauss_outer_ne (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (κ : ℝ) (hκ : κ ≠ 0) (hκv : κ * v = 2 * m) :
    ∫⁻ x, ENNReal.ofReal (max x 0 * (1 - Real.exp (-κ * max x 0)) / κ) ∂(gaussianReal m v) =
      ENNReal.ofReal (v / 2) := by
  have hv' : (v:ℝ) ≠ 0 := by exact_mod_cast hv
  have hk : 2 * m / v = κ := by rw [← hκv]; field_simp
  have href := gauss_reflect m v hv (fun y => ENNReal.ofReal (-y)) (by fun_prop)
  rw [hk] at href
  simp only [neg_neg] at href
  have hψl : ∫⁻ x, ENNReal.ofReal (max x 0 * Real.exp (-κ * max x 0)) ∂(gaussianReal m v) =
      ∫⁻ y in Set.Ici 0, ENNReal.ofReal y * ENNReal.ofReal (Real.exp (-κ * y)) ∂(gaussianReal m v) := by
    rw [← lintegral_indicator measurableSet_Ici]
    congr 1; ext y
    by_cases hy : 0 ≤ y
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hy), max_eq_left hy, ENNReal.ofReal_mul hy]
    · rw [Set.indicator_of_notMem (by simpa using hy), max_eq_right (le_of_not_ge hy)]; simp
  have hnl : ∫⁻ x, ENNReal.ofReal (max (-x) 0) ∂(gaussianReal m v) =
      ∫⁻ y in Set.Iic 0, ENNReal.ofReal (-y) ∂(gaussianReal m v) := by
    rw [← lintegral_indicator measurableSet_Iic]
    congr 1; ext y
    by_cases hy : y ≤ 0
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (by simpa using hy), max_eq_right (by linarith)]; simp
  have hint : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hpos := hint.pos_part
  have hneg := hint.neg_part
  have hneg_fin : ∫⁻ x, ENNReal.ofReal (max (-x) 0) ∂(gaussianReal m v) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hneg (ae_of_all _ (fun x => le_max_right _ _))]
    exact ENNReal.ofReal_ne_top
  have hψ_eq : ∫⁻ x, ENNReal.ofReal (max x 0 * Real.exp (-κ * max x 0)) ∂(gaussianReal m v) =
      ∫⁻ x, ENNReal.ofReal (max (-x) 0) ∂(gaussianReal m v) := by rw [hψl, hnl, href]
  have hψnn : ∀ x : ℝ, 0 ≤ max x 0 * Real.exp (-κ * max x 0) :=
    fun x => mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
  have hψint : Integrable (fun x : ℝ => max x 0 * Real.exp (-κ * max x 0)) (gaussianReal m v) := by
    have h := integrable_toReal_of_lintegral_ne_top (μ := gaussianReal m v)
      (f := fun x : ℝ => ENNReal.ofReal (max x 0 * Real.exp (-κ * max x 0)))
      (by fun_prop) (by rw [hψ_eq]; exact hneg_fin)
    refine h.congr (ae_of_all _ (fun x => ?_))
    exact ENNReal.toReal_ofReal (hψnn x)
  have hψI : ∫ x, max x 0 * Real.exp (-κ * max x 0) ∂(gaussianReal m v) =
      ∫ x, max (-x) 0 ∂(gaussianReal m v) := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max x 0 * Real.exp (-κ * max x 0))
        (ae_of_all _ hψnn) hψint.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ => max (-x) 0)
        (ae_of_all _ (fun x => le_max_right _ _)) hneg.aestronglyMeasurable, hψ_eq]
  have hPN : ∫ x, max x 0 ∂(gaussianReal m v) - ∫ x, max (-x) 0 ∂(gaussianReal m v) = m := by
    rw [← integral_sub hpos hneg]
    have : (fun x : ℝ => max x 0 - max (-x) 0) = fun x => x := by
      ext x; rcases le_total 0 x with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    rw [this]; exact integral_id_gaussianReal
  have hφ : (fun x : ℝ => max x 0 * (1 - Real.exp (-κ * max x 0)) / κ) =
      fun x => (max x 0 - max x 0 * Real.exp (-κ * max x 0)) / κ := by ext x; ring
  have hφint : Integrable (fun x : ℝ => max x 0 * (1 - Real.exp (-κ * max x 0)) / κ)
      (gaussianReal m v) := by
    rw [hφ]; exact (hpos.sub hψint).div_const κ
  have hφnn : 0 ≤ᵐ[gaussianReal m v] (fun x : ℝ => max x 0 * (1 - Real.exp (-κ * max x 0)) / κ) := by
    refine ae_of_all _ (fun x => ?_)
    have hy := le_max_right x 0
    rcases lt_or_gt_of_ne hκ with h | h
    · apply div_nonneg_of_nonpos _ h.le
      apply mul_nonpos_of_nonneg_of_nonpos hy
      have : 1 ≤ Real.exp (-κ * max x 0) := Real.one_le_exp (by nlinarith)
      linarith
    · apply div_nonneg _ h.le
      apply mul_nonneg hy
      have : Real.exp (-κ * max x 0) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hφint hφnn, hφ, integral_div,
    integral_sub hpos hψint, hψI, hPN]
  congr 1
  rw [div_eq_iff hκ]
  linear_combination (-1/2 : ℝ) * hκv

/-- Outer Gaussian computation, `κ = 0` (so `m = 0`). -/
lemma gauss_outer_zero (v : ℝ≥0) (hv : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (max x 0 * max x 0) ∂(gaussianReal 0 v) = ENNReal.ofReal (v / 2) := by
  have href := gauss_reflect 0 v hv (fun y => ENNReal.ofReal (y * y)) (by fun_prop)
  simp only [mul_zero, zero_div, neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one,
    neg_mul_neg] at href
  have hA : ∫⁻ x, ENNReal.ofReal (max x 0 * max x 0) ∂(gaussianReal 0 v) =
      ∫⁻ y in Set.Ici 0, ENNReal.ofReal (y * y) ∂(gaussianReal 0 v) := by
    rw [← lintegral_indicator measurableSet_Ici]; congr 1; ext y
    by_cases hy : 0 ≤ y
    · rw [Set.indicator_of_mem (Set.mem_Ici.2 hy), max_eq_left hy]
    · rw [Set.indicator_of_notMem (by simpa using hy), max_eq_right (le_of_not_ge hy)]; simp
  have hB : ∫⁻ x, ENNReal.ofReal (max (-x) 0 * max (-x) 0) ∂(gaussianReal 0 v) =
      ∫⁻ y in Set.Iic 0, ENNReal.ofReal (y * y) ∂(gaussianReal 0 v) := by
    rw [← lintegral_indicator measurableSet_Iic]; congr 1; ext y
    by_cases hy : y ≤ 0
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), max_eq_left (by linarith), neg_mul_neg]
    · rw [Set.indicator_of_notMem (by simpa using hy), max_eq_right (by linarith)]; simp
  have hsum : ∫⁻ x, ENNReal.ofReal (x * x) ∂(gaussianReal 0 v) =
      ∫⁻ x, ENNReal.ofReal (max x 0 * max x 0) ∂(gaussianReal 0 v) +
      ∫⁻ x, ENNReal.ofReal (max (-x) 0 * max (-x) 0) ∂(gaussianReal 0 v) := by
    rw [← lintegral_add_left (by fun_prop)]
    congr 1; ext x
    rw [← ENNReal.ofReal_add (mul_nonneg (le_max_right _ _) (le_max_right _ _))
      (mul_nonneg (le_max_right _ _) (le_max_right _ _))]
    congr 1
    rcases le_total 0 x with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have hvar : ∫⁻ x, ENNReal.ofReal (x * x) ∂(gaussianReal 0 v) = ENNReal.ofReal v := by
    have h2 : Integrable (fun x : ℝ => x * x) (gaussianReal 0 v) := by
      have := (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)).integrable_sq
      simpa [sq] using this
    rw [← ofReal_integral_eq_lintegral_ofReal h2 (ae_of_all _ (fun x => mul_self_nonneg x))]
    congr 1
    have := variance_fun_id_gaussianReal (μ := 0) (v := v)
    rw [variance_eq_integral (by fun_prop)] at this
    simpa [integral_id_gaussianReal, sq] using this
  have key : ∫⁻ y in Set.Ici 0, ENNReal.ofReal (y * y) ∂(gaussianReal 0 v) +
      ∫⁻ y in Set.Ici 0, ENNReal.ofReal (y * y) ∂(gaussianReal 0 v) =
      ENNReal.ofReal (v / 2) + ENNReal.ofReal (v / 2) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves, ← hvar, hsum, hA, hB, href]
  rw [hA]
  rw [← two_mul, ← two_mul] at key
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).1 key

open RogersSatchell.Unbiased in
lemma hasLaw_logPrice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c σ : ℝ) (t : ℝ≥0) :
    HasLaw (logPrice σ c B t) (gaussianReal (c * t) (⟨σ ^ 2, sq_nonneg σ⟩ * t)) P := by
  have h := hB.hasLaw_eval t
  have h2 : HasLaw (fun x : ℝ => σ * x + c * t) (gaussianReal (c * t) (⟨σ ^ 2, sq_nonneg σ⟩ * t))
      (gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun x : ℝ => σ * x + c * t) = (fun x => x + c * t) ∘ (fun x => σ * x) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1; ring
  exact h2.comp h

open RogersSatchell.Unbiased in
lemma cont_path {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (ω : Ω) : Continuous fun u : ℝ≥0 => logPrice σ c B u ω :=
  (continuous_const.mul (hcont ω)).add (continuous_const.mul NNReal.continuous_coe)

open RogersSatchell.Unbiased in
lemma le_runMax {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) (ω : Ω) {u : ℝ≥0} (hu : u ∈ Set.Icc 0 t) :
    logPrice σ c B u ω ≤ runMax σ c B t ω :=
  le_csSup ((isCompact_Icc.image (cont_path hcont σ c ω)).bddAbove) ⟨u, hu, rfl⟩

open RogersSatchell.Unbiased in
lemma aemeasurable_runMax {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) : AEMeasurable (runMax σ c B t) P := by
  let u : ℝ → ℝ≥0 := fun r => (min r t).toNNReal
  have hu : Continuous u := continuous_real_toNNReal.comp (continuous_id.min continuous_const)
  have hmem : ∀ r, u r ∈ Set.Icc 0 t := fun r => ⟨zero_le, by
      show (min r t).toNNReal ≤ t
      rw [Real.toNNReal_le_iff_le_coe]; exact min_le_right _ _⟩
  have hfix : ∀ v ∈ Set.Icc (0:ℝ≥0) t, u v = v := fun v hv => by
    show (min (v:ℝ) t).toNNReal = v
    rw [min_eq_left (NNReal.coe_le_coe.2 hv.2), Real.toNNReal_coe]
  refine AEMeasurable.isLUB (f := fun (q : ℚ) ω => logPrice σ c B (u q) ω)
    (fun q => ?_) (ae_of_all _ (fun ω => ?_))
  · exact ((hB.aemeasurable (u q)).const_mul σ).add_const _
  · have hX := cont_path hcont σ c ω
    have hK : BddAbove ((fun v => logPrice σ c B v ω) '' Set.Icc 0 t) :=
      (isCompact_Icc.image hX).bddAbove
    have hne : ((fun v => logPrice σ c B v ω) '' Set.Icc 0 t).Nonempty :=
      ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    have hL := isLUB_csSup hne hK
    refine ⟨?_, ?_⟩
    · rintro y ⟨q, rfl⟩
      exact hL.1 ⟨u q, hmem q, rfl⟩
    · intro b hb
      apply hL.2
      rintro y ⟨v, hv, rfl⟩
      have hg : Continuous fun r : ℝ => logPrice σ c B (u r) ω := hX.comp hu
      have := Rat.denseRange_cast.induction_on (p := fun r : ℝ => logPrice σ c B (u r) ω ≤ b)
        (v : ℝ) (isClosed_le hg continuous_const) (fun q => hb ⟨q, rfl⟩)
      rw [hfix v hv] at this
      exact this

open RogersSatchell.Unbiased in
/-- Parent from the joint-law child `R` (taken as hypothesis `hR`), main case `σ > 0`, `t ≠ 0`. -/
lemma main_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (ht : t ≠ 0)
    (hR : ∀ a : ℝ, 0 < a →
      ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => ENNReal.ofReal (2 * a - logPrice σ c B t ω)) ω ∂P =
      ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => ENNReal.ofReal (2 * a - (2 * a - logPrice σ c B t ω)) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P) :
    ∫⁻ ω, ENNReal.ofReal (runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) ∂P =
      ENNReal.ofReal (σ ^ 2 * t / 2) := by
  have hlaw := hasLaw_logPrice hB c σ t
  have hXm : AEMeasurable (logPrice σ c B t) P := hlaw.aemeasurable
  have hSm : AEMeasurable (runMax σ c B t) P := aemeasurable_runMax hB hcont σ c t
  have hXS : ∀ ω, logPrice σ c B t ω ≤ runMax σ c B t ω :=
    fun ω => le_runMax hcont σ c t ω ⟨zero_le, le_rfl⟩
  have hS0 : ∀ᵐ ω ∂P, 0 ≤ runMax σ c B t ω := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    have := le_runMax hcont σ c t ω (u := 0) ⟨le_rfl, zero_le⟩
    simp only [logPrice, Pi.zero_apply] at hω this
    simpa [hω] using this
  set v : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩ * t with hvdef
  set N := gaussianReal (c * t) v with hN
  set κ := 2 * c / σ ^ 2 with hκ
  set S' := hSm.mk (runMax σ c B t) with hS'
  set X' := hXm.mk (logPrice σ c B t) with hX'
  have hS'm : Measurable S' := hSm.measurable_mk
  have hX'm : Measurable X' := hXm.measurable_mk
  let h : ℝ → ℝ → ENNReal := fun a x =>
    Set.indicator {x | a ≤ x} (fun x => ENNReal.ofReal x * ENNReal.ofReal (Real.exp (κ * (a - x)))) x
  have hstep : ∀ a, 0 < a → ∫⁻ ω, Set.indicator {a | a ≤ S' ω ∧ X' ω ≤ a}
      (fun a => ENNReal.ofReal (2 * a - X' ω)) a ∂P = ∫⁻ x, h a x ∂N := by
    intro a ha
    have hg : Measurable fun y : ℝ => ENNReal.ofReal (2 * a - y) := by fun_prop
    have e1 : ∫⁻ ω, Set.indicator {a | a ≤ S' ω ∧ X' ω ≤ a}
        (fun a => ENNReal.ofReal (2 * a - X' ω)) a ∂P =
        ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
          (fun ω => (fun y : ℝ => ENNReal.ofReal (2 * a - y)) (logPrice σ c B t ω)) ω ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hSm.ae_eq_mk, hXm.ae_eq_mk] with ω h1 h2
      simp only [hS', hX', ← h1, ← h2, Set.indicator, Set.mem_setOf_eq]
    rw [e1, hR a ha]
    have e2 : ∀ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => (fun y : ℝ => ENNReal.ofReal (2 * a - y)) (2 * a - logPrice σ c B t ω) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω =
        h a (logPrice σ c B t ω) := by
      intro ω
      simp only [h, Set.indicator, Set.mem_setOf_eq, sub_sub_cancel]
      rw [show 2 * c * (a - logPrice σ c B t ω) / σ ^ 2 = κ * (a - logPrice σ c B t ω) by
        rw [hκ]; ring]
    simp_rw [e2]
    have hha : Measurable (h a) := Measurable.indicator
      (f := fun x : ℝ => ENNReal.ofReal x * ENNReal.ofReal (Real.exp (κ * (a - x))))
      (by fun_prop) (measurableSet_le measurable_const measurable_id)
    rw [← lintegral_map' (f := h a) hha.aemeasurable hXm, hlaw.map_eq]
  have hmeasF : Measurable (Function.uncurry fun ω a => Set.indicator {a | a ≤ S' ω ∧ X' ω ≤ a}
      (fun a => ENNReal.ofReal (2 * a - X' ω)) a) := by
    have hs : MeasurableSet {p : Ω × ℝ | p.2 ≤ S' p.1 ∧ X' p.1 ≤ p.2} :=
      (measurableSet_le measurable_snd (hS'm.comp measurable_fst)).inter
        (measurableSet_le (hX'm.comp measurable_fst) measurable_snd)
    exact Measurable.indicator (f := fun p : Ω × ℝ => ENNReal.ofReal (2 * p.2 - X' p.1))
      (by fun_prop) hs
  have hmeasH : Measurable (Function.uncurry h) := by
    exact Measurable.indicator (f := fun p : ℝ × ℝ => ENNReal.ofReal p.2 *
        ENNReal.ofReal (Real.exp (κ * (p.1 - p.2))))
      (by fun_prop) (measurableSet_le measurable_fst measurable_snd)
  have hvR : (v : ℝ) = σ ^ 2 * t := by
    rw [hvdef]; first | rfl | (rw [NNReal.coe_mul]; rfl) | simp
  have hv : v ≠ 0 := by
    intro h0
    have h1 := congrArg NNReal.toReal h0
    rw [hvR, NNReal.coe_zero] at h1
    exact (mul_ne_zero (pow_ne_zero 2 hσ.ne') (NNReal.coe_ne_zero.2 ht)) h1
  calc ∫⁻ ω, ENNReal.ofReal (runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) ∂P
      = ∫⁻ ω, (∫⁻ a in Set.Ioi (0:ℝ), Set.indicator {a | a ≤ S' ω ∧ X' ω ≤ a}
          (fun a => ENNReal.ofReal (2 * a - X' ω)) a) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hSm.ae_eq_mk, hXm.ae_eq_mk, hS0] with ω h1 h2 h3
        simp only [hS', hX', ← h1, ← h2]
        exact pw _ _ h3 (hXS ω)
    _ = ∫⁻ a in Set.Ioi (0:ℝ), ∫⁻ ω, Set.indicator {a | a ≤ S' ω ∧ X' ω ≤ a}
          (fun a => ENNReal.ofReal (2 * a - X' ω)) a ∂P :=
        lintegral_lintegral_swap hmeasF.aemeasurable
    _ = ∫⁻ a in Set.Ioi (0:ℝ), ∫⁻ x, h a x ∂N :=
        lintegral_congr_ae (ae_restrict_of_forall_mem measurableSet_Ioi (fun a ha => hstep a ha))
    _ = ∫⁻ x, (∫⁻ a in Set.Ioi (0:ℝ), h a x) ∂N :=
        lintegral_lintegral_swap hmeasH.aemeasurable
    _ = ENNReal.ofReal (σ ^ 2 * t / 2) := by
        have hh : ∀ x a, h a x = Set.indicator (Set.Iic x)
            (fun a => ENNReal.ofReal x * ENNReal.ofReal (Real.exp (κ * (a - x)))) a := by
          intro x a; simp only [h, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
        simp_rw [hh]
        rcases eq_or_ne c 0 with hc | hc
        · have hκ0 : κ = 0 := by rw [hκ, hc]; simp
          have hN0 : N = gaussianReal 0 v := by rw [hN, hc, zero_mul]
          rw [hκ0, hN0]
          simp_rw [inner_eval_zero]
          rw [gauss_outer_zero _ hv, hvR]
        · have hκne : κ ≠ 0 := by rw [hκ]; exact div_ne_zero (mul_ne_zero two_ne_zero hc) (by positivity)
          simp_rw [inner_eval_ne κ _ hκne]
          rw [gauss_outer_ne (c * t) v hv κ hκne (by
            rw [hvR, hκ, div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring), hvR]

open RogersSatchell.Unbiased in
/-- The parent `max_term_mean` from the joint-law child `R` (hypothesis `hR`). -/
theorem parent_of_R {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0)
    (hR : 0 < σ → t ≠ 0 → ∀ a : ℝ, 0 < a →
      ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => ENNReal.ofReal (2 * a - logPrice σ c B t ω)) ω ∂P =
      ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => ENNReal.ofReal (2 * a - (2 * a - logPrice σ c B t ω)) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P) :
    Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by
  have hXm := (hasLaw_logPrice hB c σ t).aemeasurable
  have hSm := aemeasurable_runMax hB hcont σ c t
  have hFm : AEStronglyMeasurable
      (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P :=
    (hSm.mul (hSm.sub hXm)).aestronglyMeasurable
  have hdeg : (∀ ω, runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) = 0) →
      σ ^ 2 * (t : ℝ) / 2 = 0 →
      Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P ∧
      ∫ ω, runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by
    intro hz hval
    refine ⟨(integrable_zero _ _ P).congr (ae_of_all _ (fun ω => (hz ω).symm)), ?_⟩
    simp only [hz, integral_zero, hval]
  rcases hσ.lt_or_eq with hσp | hσ0
  · rcases eq_or_ne t 0 with ht | ht
    · subst ht
      refine hdeg (fun ω => ?_) (by simp)
      have : runMax σ c B 0 ω = logPrice σ c B 0 ω := by
        show sSup _ = _
        rw [Set.Icc_self, Set.image_singleton, csSup_singleton]
      rw [this, sub_self, mul_zero]
    · have hF0 : ∀ᵐ ω ∂P, 0 ≤ runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) := by
        filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
        have h0 := le_runMax hcont σ c t ω (u := 0) ⟨le_rfl, zero_le⟩
        have h1 := le_runMax hcont σ c t ω (u := t) ⟨zero_le, le_rfl⟩
        simp only [logPrice, Pi.zero_apply] at hω h0
        have h0' : 0 ≤ runMax σ c B t ω := by simpa [hω] using h0
        exact mul_nonneg h0' (sub_nonneg.2 h1)
      have hL := main_pos hB hcont c σ hσp t ht (hR hσp ht)
      have hfin : ∫⁻ ω, ENNReal.ofReal
          (runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) ∂P ≠ ⊤ := by
        rw [hL]; exact ENNReal.ofReal_ne_top
      have hint : Integrable
          (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P := by
        have := integrable_toReal_of_lintegral_ne_top hFm.aemeasurable.ennreal_ofReal hfin
        refine this.congr ?_
        filter_upwards [hF0] with ω h
        exact ENNReal.toReal_ofReal h
      refine ⟨hint, ?_⟩
      rw [integral_eq_lintegral_of_nonneg_ae hF0 hFm, hL, ENNReal.toReal_ofReal (by positivity)]
  · subst hσ0
    refine hdeg (fun ω => ?_) (by simp)
    have hgr : IsGreatest ((fun u => logPrice 0 c B u ω) '' Set.Icc 0 t) (max (c * t) 0) := by
      constructor
      · rcases le_total 0 c with hc | hc
        · refine ⟨t, ⟨zero_le, le_rfl⟩, ?_⟩
          simp only [logPrice, zero_mul, zero_add]
          rw [max_eq_left (mul_nonneg hc (NNReal.coe_nonneg t))]
        · refine ⟨0, ⟨le_rfl, zero_le⟩, ?_⟩
          simp only [logPrice, zero_mul, zero_add, NNReal.coe_zero, mul_zero]
          rw [max_eq_right (by nlinarith [NNReal.coe_nonneg t])]
      · rintro y ⟨u, hu, rfl⟩
        simp only [logPrice, zero_mul, zero_add]
        rcases le_total 0 c with hc | hc
        · exact le_max_of_le_left (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.2 hu.2) hc)
        · exact le_max_of_le_right (by nlinarith [NNReal.coe_nonneg u])
    have hS : runMax 0 c B t ω = max (c * t) 0 := hgr.csSup_eq
    rw [hS]
    simp only [logPrice, zero_mul, zero_add]
    rcases le_total 0 (c * t) with h | h
    · rw [max_eq_left h]; ring
    · rw [max_eq_right h]; ring

open RogersSatchell.Unbiased in
lemma hasLaw_logPrice' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c σ : ℝ) (t : ℝ≥0) :
    ∃ v : ℝ≥0, (v : ℝ) = σ ^ 2 * t ∧ HasLaw (logPrice σ c B t) (gaussianReal (c * t) v) P :=
  ⟨_, by first | rfl | (rw [NNReal.coe_mul]; rfl) | simp, hasLaw_logPrice hB c σ t⟩

open RogersSatchell.Unbiased in
/-- Child `R` (joint law of max and close) from the first-passage strong Markov identity `R1`
(hypothesis `hR1`) and the Gaussian reflection `gauss_reflect`. -/
theorem R_of_R1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (a : ℝ) (g : ℝ → ENNReal) (hg : Measurable g)
    (hR1 : ∀ f : ℝ → ENNReal, Measurable f →
      ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω} (fun ω => f (logPrice σ c B t ω - a)) ω ∂P =
      ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
        (fun ω => ∫⁻ ω', f (logPrice σ c B (t - sInf {u : ℝ≥0 | a ≤ logPrice σ c B u ω}) ω') ∂P)
          ω ∂P) :
    ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
      (fun ω => g (logPrice σ c B t ω)) ω ∂P =
    ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
      (fun ω => g (2 * a - logPrice σ c B t ω) *
        ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P := by
  set κ := 2 * c / σ ^ 2 with hκ
  let f : ℝ → ENNReal := fun y => Set.indicator (Set.Iic 0) (fun y => g (y + a)) y
  let f' : ℝ → ENNReal := fun y => Set.indicator (Set.Ici 0)
    (fun y => g (a - y) * ENNReal.ofReal (Real.exp (-κ * y))) y
  have hfm : Measurable f := Measurable.indicator (by fun_prop) measurableSet_Iic
  have hf'm : Measurable f' := Measurable.indicator (by fun_prop) measurableSet_Ici
  have hF : ∀ r : ℝ≥0, ∫⁻ ω, f (logPrice σ c B r ω) ∂P = ∫⁻ ω, f' (logPrice σ c B r ω) ∂P := by
    intro r
    obtain ⟨v, hvR, hl⟩ := hasLaw_logPrice' hB c σ r
    rw [← lintegral_map' (f := f) hfm.aemeasurable hl.aemeasurable,
      ← lintegral_map' (f := f') hf'm.aemeasurable hl.aemeasurable, hl.map_eq]
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have hv0 : v = 0 := NNReal.coe_eq_zero.1 (by rw [hvR]; simp)
      rw [hv0, gaussianReal_zero_var, lintegral_dirac, lintegral_dirac]
      simp [f, f']
    · have hr' : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hr
      have hv0 : v ≠ 0 := by
        intro h0
        have h1 := congrArg NNReal.toReal h0
        rw [hvR, NNReal.coe_zero] at h1
        exact (mul_ne_zero (pow_ne_zero 2 hσ.ne') hr') h1
      have href := gauss_reflect (c * r) v hv0 (fun y => g (y + a)) (by fun_prop)
      have hk : 2 * (c * r) / (v : ℝ) = κ := by
        rw [hvR, hκ, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hσ.ne') hr')
          (pow_ne_zero 2 hσ.ne')]
        ring
      rw [hk] at href
      simp only [f, f']
      rw [lintegral_indicator measurableSet_Iic, lintegral_indicator measurableSet_Ici, href]
      congr 1; ext y; rw [neg_add_eq_sub]
  have hXS : ∀ ω, logPrice σ c B t ω ≤ runMax σ c B t ω :=
    fun ω => le_runMax hcont σ c t ω ⟨zero_le, le_rfl⟩
  calc ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => g (logPrice σ c B t ω)) ω ∂P
      = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => f (logPrice σ c B t ω - a)) ω ∂P := by
        refine lintegral_congr (fun ω => ?_)
        by_cases h1 : a ≤ runMax σ c B t ω <;> by_cases h2 : logPrice σ c B t ω ≤ a <;>
          simp [Set.indicator, f, h1, h2, sub_nonpos]
    _ = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => ∫⁻ ω', f (logPrice σ c B (t - sInf {u : ℝ≥0 | a ≤ logPrice σ c B u ω}) ω') ∂P)
            ω ∂P := hR1 f hfm
    _ = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => ∫⁻ ω', f' (logPrice σ c B (t - sInf {u : ℝ≥0 | a ≤ logPrice σ c B u ω}) ω') ∂P)
            ω ∂P := by simp_rw [hF]
    _ = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => f' (logPrice σ c B t ω - a)) ω ∂P := (hR1 f' hf'm).symm
    _ = _ := by
        refine lintegral_congr (fun ω => ?_)
        by_cases h1 : a ≤ logPrice σ c B t ω
        · have h2 : a ≤ runMax σ c B t ω := h1.trans (hXS ω)
          have h3 : 0 ≤ logPrice σ c B t ω - a := sub_nonneg.2 h1
          simp only [Set.indicator, Set.mem_setOf_eq, f', Set.mem_Ici, h1, h2, h3, if_true]
          rw [show a - (logPrice σ c B t ω - a) = 2 * a - logPrice σ c B t ω by ring,
            show -κ * (logPrice σ c B t ω - a) = 2 * c * (a - logPrice σ c B t ω) / σ ^ 2 by
              rw [hκ]; ring]
        · have h3 : ¬ 0 ≤ logPrice σ c B t ω - a := by rw [sub_nonneg]; exact h1
          by_cases h2 : a ≤ runMax σ c B t ω <;> simp [Set.indicator, f', h1, h2, h3]

end RSMaxTerm

namespace RSMaxTermR1

open RogersSatchell.Unbiased in
lemma hasLaw_logPrice {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c σ : ℝ) (t : ℝ≥0) :
    HasLaw (logPrice σ c B t) (gaussianReal (c * t) (⟨σ ^ 2, sq_nonneg σ⟩ * t)) P := by
  have h := hB.hasLaw_eval t
  have h2 : HasLaw (fun x : ℝ => σ * x + c * t) (gaussianReal (c * t) (⟨σ ^ 2, sq_nonneg σ⟩ * t))
      (gaussianReal 0 t) := by
    refine ⟨by fun_prop, ?_⟩
    have : (fun x : ℝ => σ * x + c * t) = (fun x => x + c * t) ∘ (fun x => σ * x) := rfl
    rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1; ring
  exact h2.comp h

open RogersSatchell.Unbiased in
lemma cont_path {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (ω : Ω) : Continuous fun u : ℝ≥0 => logPrice σ c B u ω :=
  (continuous_const.mul (hcont ω)).add (continuous_const.mul NNReal.continuous_coe)

open RogersSatchell.Unbiased in
lemma le_runMax {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) (ω : Ω) {u : ℝ≥0} (hu : u ∈ Set.Icc 0 t) :
    logPrice σ c B u ω ≤ runMax σ c B t ω :=
  le_csSup ((isCompact_Icc.image (cont_path hcont σ c ω)).bddAbove) ⟨u, hu, rfl⟩

open RogersSatchell.Unbiased in
lemma aemeasurable_runMax {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) : AEMeasurable (runMax σ c B t) P := by
  let u : ℝ → ℝ≥0 := fun r => (min r t).toNNReal
  have hu : Continuous u := continuous_real_toNNReal.comp (continuous_id.min continuous_const)
  have hmem : ∀ r, u r ∈ Set.Icc 0 t := fun r => ⟨zero_le, by
      show (min r t).toNNReal ≤ t
      rw [Real.toNNReal_le_iff_le_coe]; exact min_le_right _ _⟩
  have hfix : ∀ v ∈ Set.Icc (0:ℝ≥0) t, u v = v := fun v hv => by
    show (min (v:ℝ) t).toNNReal = v
    rw [min_eq_left (NNReal.coe_le_coe.2 hv.2), Real.toNNReal_coe]
  refine AEMeasurable.isLUB (f := fun (q : ℚ) ω => logPrice σ c B (u q) ω)
    (fun q => ?_) (ae_of_all _ (fun ω => ?_))
  · exact ((hB.aemeasurable (u q)).const_mul σ).add_const _
  · have hX := cont_path hcont σ c ω
    have hK : BddAbove ((fun v => logPrice σ c B v ω) '' Set.Icc 0 t) :=
      (isCompact_Icc.image hX).bddAbove
    have hne : ((fun v => logPrice σ c B v ω) '' Set.Icc 0 t).Nonempty :=
      ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    have hL := isLUB_csSup hne hK
    refine ⟨?_, ?_⟩
    · rintro y ⟨q, rfl⟩
      exact hL.1 ⟨u q, hmem q, rfl⟩
    · intro b hb
      apply hL.2
      rintro y ⟨v, hv, rfl⟩
      have hg : Continuous fun r : ℝ => logPrice σ c B (u r) ω := hX.comp hu
      have := Rat.denseRange_cast.induction_on (p := fun r : ℝ => logPrice σ c B (u r) ω ≤ b)
        (v : ℝ) (isClosed_le hg continuous_const) (fun q => hb ⟨q, rfl⟩)
      rw [hfix v hv] at this
      exact this

open RogersSatchell.Unbiased in
lemma runMax_mono {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (ω : Ω) {u u' : ℝ≥0} (h : u ≤ u') :
    runMax σ c B u ω ≤ runMax σ c B u' ω :=
  csSup_le_csSup ((isCompact_Icc.image (cont_path hcont σ c ω)).bddAbove)
    ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩ (Set.image_mono (Set.Icc_subset_Icc_right h))

open RogersSatchell.Unbiased in
lemma runMax_mem {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (u : ℝ≥0) (ω : Ω) :
    ∃ v ∈ Set.Icc (0:ℝ≥0) u, logPrice σ c B v ω = runMax σ c B u ω :=
  (isCompact_Icc.image (cont_path hcont σ c ω)).sSup_mem ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩

open RogersSatchell.Unbiased in
lemma runMax_past {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) {u s : ℝ≥0} (hus : u ≤ s) :
    ∃ Ψ : (Set.Iic s → ℝ) → ℝ, Measurable Ψ ∧
      ∀ ω, runMax σ c B u ω = Ψ (fun v : Set.Iic s => B v ω) := by
  let cl : ℝ → ℝ≥0 := fun r => (min r u).toNNReal
  have hcl : Continuous cl := continuous_real_toNNReal.comp (continuous_id.min continuous_const)
  have hmem : ∀ r, cl r ∈ Set.Icc 0 u := fun r => ⟨zero_le, by
      show (min r u).toNNReal ≤ u
      rw [Real.toNNReal_le_iff_le_coe]; exact min_le_right _ _⟩
  have hfix : ∀ v ∈ Set.Icc (0:ℝ≥0) u, cl v = v := fun v hv => by
    show (min (v:ℝ) u).toNNReal = v
    rw [min_eq_left (NNReal.coe_le_coe.2 hv.2), Real.toNNReal_coe]
  let w : ℚ → Set.Iic s := fun q => ⟨cl q, (hmem q).2.trans hus⟩
  refine ⟨fun p => ⨆ q : ℚ, (σ * p (w q) + c * ((w q : ℝ≥0) : ℝ)), ?_, fun ω => ?_⟩
  · exact Measurable.iSup (fun q => (by fun_prop :
      Measurable fun p : Set.Iic s → ℝ => σ * p (w q) + c * ((w q : ℝ≥0) : ℝ)))
  · symm
    apply IsLUB.ciSup_eq
    have hX := cont_path hcont σ c ω
    have hK : BddAbove ((fun v => logPrice σ c B v ω) '' Set.Icc 0 u) :=
      (isCompact_Icc.image hX).bddAbove
    have hne : ((fun v => logPrice σ c B v ω) '' Set.Icc 0 u).Nonempty :=
      ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩
    have hL := isLUB_csSup hne hK
    rw [show runMax σ c B u ω = sSup ((fun v => logPrice σ c B v ω) '' Set.Icc 0 u) from rfl]
    refine ⟨?_, ?_⟩
    · rintro y ⟨q, rfl⟩
      exact hL.1 ⟨cl q, hmem q, rfl⟩
    · intro b hb
      apply hL.2
      rintro y ⟨v, hv, rfl⟩
      have hg : Continuous fun r : ℝ => logPrice σ c B (cl r) ω := hX.comp hcl
      have := Rat.denseRange_cast.induction_on (p := fun r : ℝ => logPrice σ c B (cl r) ω ≤ b)
        (v : ℝ) (isClosed_le hg continuous_const) (fun q => hb ⟨q, rfl⟩)
      rw [hfix v hv] at this
      exact this

open RogersSatchell.Unbiased in
/-- Weak Markov at a deterministic time `s ≤ t`, lintegral form. -/
lemma markov_term {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c σ : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set (Set.Iic s → ℝ)) (hA : MeasurableSet A) (E : Set Ω)
    (hE : E = (fun ω (v : Set.Iic s) => B v ω) ⁻¹' A) (hEm : NullMeasurableSet E P)
    (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ ω, Set.indicator E (fun ω => f (logPrice σ c B t ω - logPrice σ c B s ω)) ω ∂P =
      P E * ∫⁻ ω, f (logPrice σ c B (t - s) ω) ∂P := by
  subst hE
  set Z := fun ω (v : Set.Iic s) => B v ω with hZ
  set Y := fun ω (r : ℝ≥0) => B (s + r) ω - B s ω with hY
  have hind : IndepFun Y Z P := hB.indepFun_shift s
  let φ : (ℝ≥0 → ℝ) → ENNReal := fun p => f (σ * p (t - s) + c * ((t - s : ℝ≥0) : ℝ))
  have hφ : Measurable φ := hf.comp (by fun_prop :
    Measurable fun p : ℝ≥0 → ℝ => σ * p (t - s) + c * ((t - s : ℝ≥0) : ℝ))
  have hψ : Measurable (A.indicator (fun _ => (1 : ENNReal))) := measurable_const.indicator hA
  have hind2 := hind.comp hφ hψ
  have hYm : AEMeasurable (fun ω => B (s + (t - s)) ω - B s ω) P :=
    (hB.aemeasurable _).sub (hB.aemeasurable _)
  have hφYm : AEMeasurable (φ ∘ Y) P := hf.comp_aemeasurable ((hYm.const_mul σ).add_const _)
  have hcomp : (A.indicator fun _ => (1:ENNReal)) ∘ Z = (Z ⁻¹' A).indicator 1 := by
    funext ω
    by_cases h : Z ω ∈ A
    · rw [Function.comp_apply, Set.indicator_of_mem h,
        Set.indicator_of_mem (show ω ∈ Z ⁻¹' A from h)]; rfl
    · rw [Function.comp_apply, Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show ω ∉ Z ⁻¹' A from h)]
  have hψZm : AEMeasurable ((A.indicator fun _ => (1:ENNReal)) ∘ Z) P := by
    rw [hcomp]; exact aemeasurable_const.indicator₀ hEm
  have key := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' hφYm hψZm hind2
  have hts : s + (t - s) = t := add_tsub_cancel_of_le hst
  have e1 : ∀ ω, Set.indicator (Z ⁻¹' A)
      (fun ω => f (logPrice σ c B t ω - logPrice σ c B s ω)) ω
      = ((φ ∘ Y) * ((A.indicator fun _ => (1:ENNReal)) ∘ Z)) ω := by
    intro ω
    have e : logPrice σ c B t ω - logPrice σ c B s ω =
        σ * Y ω (t - s) + c * ((t - s : ℝ≥0) : ℝ) := by
      show σ * B t ω + c * (t:ℝ) - (σ * B s ω + c * (s:ℝ)) =
        σ * (B (s + (t - s)) ω - B s ω) + c * ((t - s : ℝ≥0) : ℝ)
      rw [hts, NNReal.coe_sub hst]; ring
    rw [Pi.mul_apply, Function.comp_apply, Function.comp_apply]
    by_cases h : Z ω ∈ A
    · rw [Set.indicator_of_mem (show ω ∈ Z ⁻¹' A from h), Set.indicator_of_mem h, mul_one]
      exact congrArg f e
    · rw [Set.indicator_of_notMem (show ω ∉ Z ⁻¹' A from h), Set.indicator_of_notMem h,
        mul_zero]
  rw [lintegral_congr e1, key, mul_comm]
  congr 1
  · rw [hcomp, lintegral_indicator_one₀ hEm]
  · have h1 := hasLaw_logPrice (hB.shift s) c σ (t - s)
    have h2 := hasLaw_logPrice hB c σ (t - s)
    rw [show (∫⁻ ω, (φ ∘ Y) ω ∂P) =
        ∫⁻ ω, f (logPrice σ c (fun r ω => B (s + r) ω - B s ω) (t - s) ω) ∂P from rfl,
      ← lintegral_map' (f := f) hf.aemeasurable h1.aemeasurable,
      ← lintegral_map' (f := f) hf.aemeasurable h2.aemeasurable, h1.map_eq, h2.map_eq]

noncomputable def grid (t : ℝ≥0) (n k : ℕ) : ℝ≥0 := k * t / 2 ^ n

lemma grid_coe (t : ℝ≥0) (n k : ℕ) : ((grid t n k : ℝ≥0) : ℝ) = k * t / 2 ^ n := by
  simp [grid]

lemma grid_mono (t : ℝ≥0) (n : ℕ) {j k : ℕ} (h : j ≤ k) : grid t n j ≤ grid t n k := by
  rw [← NNReal.coe_le_coe, grid_coe, grid_coe, div_le_div_iff_of_pos_right (by positivity)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) t.2

lemma grid_top (t : ℝ≥0) (n : ℕ) : grid t n (2 ^ n) = t := by
  rw [← NNReal.coe_inj, grid_coe]; push_cast; field_simp

lemma grid_le (t : ℝ≥0) (n : ℕ) {k : ℕ} (h : k ≤ 2 ^ n) : grid t n k ≤ t :=
  (grid_mono t n h).trans_eq (grid_top t n)

lemma grid_zero (t : ℝ≥0) (n : ℕ) : grid t n 0 = 0 := by simp [grid]

lemma grid_sub (t : ℝ≥0) (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    ((grid t n k : ℝ≥0) : ℝ) - grid t n (k - 1) = t / 2 ^ n := by
  rw [grid_coe, grid_coe, Nat.cast_sub hk]; push_cast; ring

open RogersSatchell.Unbiased in
/-- First grid index at which the running max reaches `a`. -/
def Ev {Ω : Type*} (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : ℝ) (n k : ℕ) : Set Ω :=
  {ω | a ≤ runMax σ c B (grid t n k) ω ∧ runMax σ c B (grid t n (k - 1)) ω < a}

open RogersSatchell.Unbiased in
noncomputable def Phi {Ω : Type*} (σ c : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (a : ℝ)
    (f : ℝ → ENNReal) (n : ℕ) (ω : Ω) : ENNReal :=
  ∑ k ∈ Finset.range (2 ^ n + 1), (Ev σ c B t a n k).indicator
    (fun ω => f (logPrice σ c B t ω - logPrice σ c B (grid t n k) ω)) ω

lemma Ev_disj {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    {σ c : ℝ} {t : ℝ≥0} {a : ℝ} {n j k : ℕ} (hjk : j < k) {ω : Ω}
    (hj : ω ∈ Ev σ c B t a n j) (hk : ω ∈ Ev σ c B t a n k) : False := by
  simp only [Ev, Set.mem_ofPred_eq] at hj hk
  have h1 := runMax_mono hcont σ c ω (grid_mono t n (show j ≤ k - 1 by omega))
  exact absurd (hj.1.trans h1) (not_le.2 hk.2)

open RogersSatchell.Unbiased in
lemma Phi_eq_of_mem {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    {σ c : ℝ} {t : ℝ≥0} {a : ℝ} (f : ℝ → ENNReal) {n k : ℕ}
    (hk : k ∈ Finset.range (2 ^ n + 1)) {ω : Ω} (hω : ω ∈ Ev σ c B t a n k) :
    Phi σ c B t a f n ω = f (logPrice σ c B t ω - logPrice σ c B (grid t n k) ω) := by
  unfold Phi
  rw [Finset.sum_eq_single k]
  · exact Set.indicator_of_mem hω _
  · intro j _ hjk
    apply Set.indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hjk with h | h
    · exact Ev_disj hcont h hj hω
    · exact Ev_disj hcont h hω hj
  · intro h; exact absurd hk h

lemma Phi_eq_zero {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {σ c : ℝ} {t : ℝ≥0} {a : ℝ}
    (f : ℝ → ENNReal) {n : ℕ} {ω : Ω}
    (h : ∀ k ∈ Finset.range (2 ^ n + 1), ω ∉ Ev σ c B t a n k) :
    Phi σ c B t a f n ω = 0 :=
  Finset.sum_eq_zero (fun k hk => Set.indicator_of_notMem (h k hk) _)

lemma Phi_le {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    {σ c : ℝ} {t : ℝ≥0} {a : ℝ} (f : ℝ → ENNReal) {C : ENNReal} (hC : ∀ y, f y ≤ C)
    (n : ℕ) (ω : Ω) : Phi σ c B t a f n ω ≤ C := by
  by_cases h : ∃ k ∈ Finset.range (2 ^ n + 1), ω ∈ Ev σ c B t a n k
  · obtain ⟨k, hk, hω⟩ := h
    rw [Phi_eq_of_mem hcont f hk hω]; exact hC _
  · push_neg at h
    rw [Phi_eq_zero f h]; exact bot_le

lemma Ev_past {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) (a : ℝ) (n k : ℕ) :
    ∃ A : Set (Set.Iic (grid t n k) → ℝ), MeasurableSet A ∧
      Ev σ c B t a n k = (fun ω (v : Set.Iic (grid t n k)) => B v ω) ⁻¹' A := by
  obtain ⟨Ψ1, hΨ1, e1⟩ := runMax_past hcont σ c (le_refl (grid t n k))
  obtain ⟨Ψ2, hΨ2, e2⟩ := runMax_past hcont σ c (grid_mono t n (Nat.sub_le k 1))
  refine ⟨{p | a ≤ Ψ1 p ∧ Ψ2 p < a},
    (measurableSet_le measurable_const hΨ1).inter (measurableSet_lt hΨ2 measurable_const), ?_⟩
  ext ω
  simp only [Ev, Set.mem_ofPred_eq, Set.mem_preimage, e1, e2]

lemma Ev_null {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) (a : ℝ) (n k : ℕ) : NullMeasurableSet (Ev σ c B t a n k) P :=
  (nullMeasurableSet_le aemeasurable_const (aemeasurable_runMax hB hcont σ c _)).inter
    (nullMeasurableSet_lt (aemeasurable_runMax hB hcont σ c _) aemeasurable_const)

open RogersSatchell.Unbiased in
lemma term_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (t : ℝ≥0) (a : ℝ) (g : ℝ → ENNReal) (hg : Measurable g) {n k : ℕ}
    (hk : k ∈ Finset.range (2 ^ n + 1)) :
    ∫⁻ ω, (Ev σ c B t a n k).indicator
        (fun ω => g (logPrice σ c B t ω - logPrice σ c B (grid t n k) ω)) ω ∂P
      = P (Ev σ c B t a n k) * ∫⁻ ω, g (logPrice σ c B (t - grid t n k) ω) ∂P := by
  obtain ⟨A, hA, hE⟩ := Ev_past hcont σ c t a n k
  exact markov_term hB c σ (grid_le t n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))) A hA _ hE
    (Ev_null hB hcont σ c t a n k) g hg

open RogersSatchell.Unbiased in
lemma term_aemeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (t : ℝ≥0) (a : ℝ) (g : ℝ → ENNReal) (hg : Measurable g) (n k : ℕ) :
    AEMeasurable ((Ev σ c B t a n k).indicator
        (fun ω => g (logPrice σ c B t ω - logPrice σ c B (grid t n k) ω))) P := by
  exact (hg.comp_aemeasurable ((hasLaw_logPrice hB c σ t).aemeasurable.sub
    (hasLaw_logPrice hB c σ _).aemeasurable)).indicator₀ (Ev_null hB hcont σ c t a n k)

lemma Phi_aemeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (t : ℝ≥0) (a : ℝ) (g : ℝ → ENNReal) (hg : Measurable g) (n : ℕ) :
    AEMeasurable (Phi σ c B t a g n) P := by
  unfold Phi
  exact Finset.aemeasurable_fun_sum _ (fun k _ => term_aemeas hB hcont c σ t a g hg n k)

lemma disc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (t : ℝ≥0) (a : ℝ) (f f' : ℝ → ENNReal) (hf : Measurable f) (hf' : Measurable f')
    (hF : ∀ r : ℝ≥0, ∫⁻ ω, f (RogersSatchell.Unbiased.logPrice σ c B r ω) ∂P =
      ∫⁻ ω, f' (RogersSatchell.Unbiased.logPrice σ c B r ω) ∂P) (n : ℕ) :
    ∫⁻ ω, Phi σ c B t a f n ω ∂P = ∫⁻ ω, Phi σ c B t a f' n ω ∂P := by
  unfold Phi
  rw [lintegral_finsetSum' _ (fun k _ => term_aemeas hB hcont c σ t a f hf n k),
    lintegral_finsetSum' _ (fun k _ => term_aemeas hB hcont c σ t a f' hf' n k)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [term_eq hB hcont c σ t a f hf hk, term_eq hB hcont c σ t a f' hf' hk, hF]

open RogersSatchell.Unbiased in
lemma Phi_tendsto {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} (hcont : ∀ ω, Continuous fun t => B t ω)
    (σ c : ℝ) (t : ℝ≥0) (a : ℝ) (ha : 0 < a) (f : ℝ → ENNReal) (ω : Ω)
    (h0 : B 0 ω = 0) (hG : a ≤ runMax σ c B t ω)
    (hfc : ContinuousAt f (logPrice σ c B t ω - a)) :
    Tendsto (fun n => Phi σ c B t a f n ω) atTop (𝓝 (f (logPrice σ c B t ω - a))) := by
  classical
  have hex : ∀ n : ℕ, ∃ k, a ≤ runMax σ c B (grid t n k) ω :=
    fun n => ⟨2 ^ n, by rw [grid_top]; exact hG⟩
  let K : ℕ → ℕ := fun n => Nat.find (hex n)
  have hKspec : ∀ n, a ≤ runMax σ c B (grid t n (K n)) ω := fun n => Nat.find_spec (hex n)
  have hKle : ∀ n, K n ≤ 2 ^ n := fun n => Nat.find_min' (hex n) (by rw [grid_top]; exact hG)
  have hK0 : ∀ n, K n ≠ 0 := by
    intro n h
    have := hKspec n
    rw [h, grid_zero] at this
    have e : runMax σ c B 0 ω = 0 := by
      show sSup _ = _
      rw [Set.Icc_self, Set.image_singleton, csSup_singleton]
      simp [logPrice, h0]
    linarith
  have hKmin : ∀ n, runMax σ c B (grid t n (K n - 1)) ω < a := fun n =>
    not_le.1 (Nat.find_min (hex n) (show K n - 1 < K n by have := hK0 n; omega))
  have hPhi : ∀ n, Phi σ c B t a f n ω =
      f (logPrice σ c B t ω - logPrice σ c B (grid t n (K n)) ω) := fun n =>
    Phi_eq_of_mem hcont f (Finset.mem_range.2 (Nat.lt_succ_of_le (hKle n))) ⟨hKspec n, hKmin n⟩
  refine Tendsto.congr (fun n => (hPhi n).symm) ?_
  refine hfc.tendsto.comp (tendsto_const_nhds.sub ?_)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hUC := (isCompact_Icc (a := (0:ℝ≥0)) (b := t)).uniformContinuousOn_of_continuous
    (cont_path hcont σ c ω).continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨δ, hδ, hδε⟩ := hUC ε hε
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((t:ℝ) / δ) (one_lt_two : (1:ℝ) < 2)
  refine ⟨N, fun n hn => ?_⟩
  have hstep : (t:ℝ) / 2 ^ n < δ := by
    have h2 : (2:ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hk1 : 1 ≤ K n := Nat.one_le_iff_ne_zero.2 (hK0 n)
  have hgk : grid t n (K n) ≤ t := grid_le t n (hKle n)
  have hg1k : grid t n (K n - 1) ≤ grid t n (K n) := grid_mono t n (Nat.sub_le _ 1)
  obtain ⟨v, hv, hXv⟩ := runMax_mem hcont σ c (grid t n (K n)) ω
  have hva : a ≤ logPrice σ c B v ω := hXv ▸ hKspec n
  have hv1 : grid t n (K n - 1) < v := by
    by_contra hcon
    push_neg at hcon
    have := le_runMax hcont σ c (grid t n (K n - 1)) ω (u := v) ⟨zero_le, hcon⟩
    linarith [hKmin n]
  have hX1 : logPrice σ c B (grid t n (K n - 1)) ω < a :=
    lt_of_le_of_lt (le_runMax hcont σ c _ ω ⟨zero_le, le_rfl⟩) (hKmin n)
  have hdiff := grid_sub t n hk1
  have hmemt : ∀ u, u ≤ grid t n (K n) → u ∈ Set.Icc (0:ℝ≥0) t :=
    fun u hu => ⟨zero_le, hu.trans hgk⟩
  have hvle : (v : ℝ) ≤ grid t n (K n) := NNReal.coe_le_coe.2 hv.2
  have hv1' : ((grid t n (K n - 1) : ℝ≥0) : ℝ) < v := NNReal.coe_lt_coe.2 hv1
  have d1 : dist (grid t n (K n)) v < δ := by
    rw [NNReal.dist_eq, abs_of_nonneg (by linarith)]
    linarith
  have d2 : dist (grid t n (K n)) (grid t n (K n - 1)) < δ := by
    rw [NNReal.dist_eq, hdiff, abs_of_nonneg (by positivity)]; exact hstep
  have e1 := hδε _ (hmemt _ le_rfl) _ (hmemt _ hv.2) d1
  have e2 := hδε _ (hmemt _ le_rfl) _ (hmemt _ hg1k) d2
  rw [Real.dist_eq] at e1 e2 ⊢
  rw [abs_lt] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

open RogersSatchell.Unbiased in
lemma ae_logPrice_ne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (ht : t ≠ 0)
    (a : ℝ) : ∀ᵐ ω ∂P, logPrice σ c B t ω ≠ a := by
  have hl := hasLaw_logPrice hB c σ t
  have hv0 : (⟨σ ^ 2, sq_nonneg σ⟩ : ℝ≥0) ≠ 0 := by
    exact NNReal.coe_ne_zero.1 (pow_ne_zero 2 hσ.ne')
  have h1 : gaussianReal (c * t) (⟨σ ^ 2, sq_nonneg σ⟩ * t) {a} = 0 :=
    gaussianReal_absolutelyContinuous _ (mul_ne_zero hv0 ht) (Real.volume_singleton)
  rw [← hl.map_eq, Measure.map_apply₀ hl.aemeasurable
    (measurableSet_singleton a).nullMeasurableSet] at h1
  rw [ae_iff]
  convert h1 using 2
  ext ω; simp

open RogersSatchell.Unbiased in
/-- Strong Markov at the first passage over `a`, pair form. -/
theorem R1pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (ht : t ≠ 0) (a : ℝ) (ha : 0 < a)
    (f f' : ℝ → ENNReal) (hf : Measurable f) (hf' : Measurable f')
    (C : ENNReal) (hC : C ≠ ⊤) (hfC : ∀ y, f y ≤ C) (hf'C : ∀ y, f' y ≤ C)
    (hfc : ∀ y, y ≠ 0 → ContinuousAt f y) (hf'c : ∀ y, y ≠ 0 → ContinuousAt f' y)
    (hF : ∀ r : ℝ≥0, ∫⁻ ω, f (logPrice σ c B r ω) ∂P = ∫⁻ ω, f' (logPrice σ c B r ω) ∂P) :
    ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω} (fun ω => f (logPrice σ c B t ω - a)) ω ∂P =
    ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
      (fun ω => f' (logPrice σ c B t ω - a)) ω ∂P := by
  have hne := ae_logPrice_ne hB c σ hσ t ht a
  have lim : ∀ g : ℝ → ENNReal, Measurable g → (∀ y, g y ≤ C) →
      (∀ y, y ≠ 0 → ContinuousAt g y) →
      Tendsto (fun n => ∫⁻ ω, Phi σ c B t a g n ω ∂P) atTop
        (𝓝 (∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => g (logPrice σ c B t ω - a)) ω ∂P)) := by
    intro g hg hgC hgc
    refine tendsto_lintegral_of_dominated_convergence' (fun _ => C)
      (fun n => Phi_aemeas hB hcont c σ t a g hg n)
      (fun n => ae_of_all _ (fun ω => Phi_le hcont g hgC n ω)) (by simpa using hC) ?_
    filter_upwards [hB.eval_zero_ae_eq_zero, hne] with ω h0 hX
    by_cases hG : a ≤ runMax σ c B t ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | a ≤ runMax σ c B t ω} from hG)]
      exact Phi_tendsto hcont σ c t a ha g ω h0 hG (hgc _ (sub_ne_zero.2 hX))
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | a ≤ runMax σ c B t ω} from hG)]
      refine tendsto_const_nhds.congr (fun n => (Phi_eq_zero g (fun k hk hω => hG ?_)).symm)
      exact hω.1.trans (runMax_mono hcont σ c ω
        (grid_le t n (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))))
  exact tendsto_nhds_unique ((lim f hf hfC hfc).congr
    (fun n => disc hB hcont c σ t a f f' hf hf' hF n)) (lim f' hf' hf'C hf'c)

end RSMaxTermR1


open Filter Topology

namespace RSMaxTerm

open RogersSatchell.Unbiased in
/-- Child `R` (joint law of max and close) from the first-passage strong Markov identity `R1`
(hypothesis `hR1`) and the Gaussian reflection `gauss_reflect`. -/
theorem R_K {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (ht : t ≠ 0) (a : ℝ) (ha : 0 < a) (g : ℝ → ENNReal)
    (hgc : Continuous g) (C : ENNReal) (hC : C ≠ ⊤) (hgC : ∀ y, g y ≤ C) (M : ℝ)
    (hgM : ∀ y, y ≤ -M → g y = 0) :
    ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
      (fun ω => g (logPrice σ c B t ω)) ω ∂P =
    ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
      (fun ω => g (2 * a - logPrice σ c B t ω) *
        ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P := by
  have hg : Measurable g := hgc.measurable
  set κ := 2 * c / σ ^ 2 with hκ
  let f : ℝ → ENNReal := fun y => Set.indicator (Set.Iic 0) (fun y => g (y + a)) y
  let f' : ℝ → ENNReal := fun y => Set.indicator (Set.Ici 0)
    (fun y => g (a - y) * ENNReal.ofReal (Real.exp (-κ * y))) y
  have hfm : Measurable f := Measurable.indicator (by fun_prop) measurableSet_Iic
  have hf'm : Measurable f' := Measurable.indicator (by fun_prop) measurableSet_Ici
  have hfC : ∀ y, f y ≤ C := fun y => by
    by_cases h : y ∈ Set.Iic (0:ℝ)
    · simp only [f]; rw [Set.indicator_of_mem h]; exact hgC _
    · simp only [f]; rw [Set.indicator_of_notMem h]; exact bot_le
  set C' := C * ENNReal.ofReal (Real.exp (|κ| * (|a| + |M|))) with hC'def
  have hC' : C' ≠ ⊤ := ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top
  have hf'C : ∀ y, f' y ≤ C' := fun y => by
    by_cases h : y ∈ Set.Ici (0:ℝ)
    · simp only [f']; rw [Set.indicator_of_mem h]
      by_cases hM : a - y ≤ -M
      · rw [hgM _ hM, zero_mul]; exact bot_le
      · push_neg at hM
        have hy : (0:ℝ) ≤ y := h
        refine mul_le_mul' (hgC _) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
        have h1 : -κ * y ≤ |κ| * y := by
          have := neg_abs_le κ; nlinarith [abs_nonneg κ]
        have h2 : y ≤ |a| + |M| := by linarith [le_abs_self a, le_abs_self M]
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg κ))
    · simp only [f']; rw [Set.indicator_of_notMem h]; exact bot_le
  have hfC2 : ∀ y, f y ≤ C + C' := fun y => (hfC y).trans le_self_add
  have hf'C2 : ∀ y, f' y ≤ C + C' := fun y => (hf'C y).trans le_add_self
  have hfc : ∀ y, y ≠ 0 → ContinuousAt f y := fun y hy => by
    rcases lt_or_gt_of_ne hy with h | h
    · have : f =ᶠ[𝓝 y] fun z => g (z + a) := by
        filter_upwards [Iio_mem_nhds h] with z hz
        simp only [f]; exact Set.indicator_of_mem (Set.mem_Iic.2 (Set.mem_Iio.1 hz).le) _
      exact ((hgc.comp (continuous_id.add continuous_const)).continuousAt).congr this.symm
    · have : f =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with z hz
        simp only [f]
        exact Set.indicator_of_notMem
          (fun h' => absurd (Set.mem_Iic.1 h') (not_le.2 (Set.mem_Ioi.1 hz))) _
      exact continuousAt_const.congr this.symm
  have hf'c : ∀ y, y ≠ 0 → ContinuousAt f' y := fun y hy => by
    rcases lt_or_gt_of_ne hy with h | h
    · have : f' =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with z hz
        simp only [f']
        exact Set.indicator_of_notMem
          (fun h' => absurd (Set.mem_Ici.1 h') (not_le.2 (Set.mem_Iio.1 hz))) _
      exact continuousAt_const.congr this.symm
    · have : f' =ᶠ[𝓝 y] fun z => g (a - z) * ENNReal.ofReal (Real.exp (-κ * z)) := by
        filter_upwards [Ioi_mem_nhds h] with z hz
        simp only [f']; exact Set.indicator_of_mem (Set.mem_Ici.2 (Set.mem_Ioi.1 hz).le) _
      have hc : ContinuousAt (fun z : ℝ => g (a - z) * ENNReal.ofReal (Real.exp (-κ * z))) y :=
        ENNReal.Tendsto.mul ((hgc.comp (continuous_const.sub continuous_id)).continuousAt)
          (Or.inr ENNReal.ofReal_ne_top)
          ((ENNReal.continuous_ofReal.comp
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousAt)
          (Or.inr (ne_top_of_le_ne_top hC (hgC _)))
      exact hc.congr this.symm
  have hF : ∀ r : ℝ≥0, ∫⁻ ω, f (logPrice σ c B r ω) ∂P = ∫⁻ ω, f' (logPrice σ c B r ω) ∂P := by
    intro r
    obtain ⟨v, hvR, hl⟩ := hasLaw_logPrice' hB c σ r
    rw [← lintegral_map' (f := f) hfm.aemeasurable hl.aemeasurable,
      ← lintegral_map' (f := f') hf'm.aemeasurable hl.aemeasurable, hl.map_eq]
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have hv0 : v = 0 := NNReal.coe_eq_zero.1 (by rw [hvR]; simp)
      rw [hv0, gaussianReal_zero_var, lintegral_dirac, lintegral_dirac]
      simp [f, f']
    · have hr' : (r : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hr
      have hv0 : v ≠ 0 := by
        intro h0
        have h1 := congrArg NNReal.toReal h0
        rw [hvR, NNReal.coe_zero] at h1
        exact (mul_ne_zero (pow_ne_zero 2 hσ.ne') hr') h1
      have href := gauss_reflect (c * r) v hv0 (fun y => g (y + a)) (by fun_prop)
      have hk : 2 * (c * r) / (v : ℝ) = κ := by
        rw [hvR, hκ, div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 hσ.ne') hr')
          (pow_ne_zero 2 hσ.ne')]
        ring
      rw [hk] at href
      simp only [f, f']
      rw [lintegral_indicator measurableSet_Iic, lintegral_indicator measurableSet_Ici, href]
      congr 1; ext y; rw [neg_add_eq_sub]
  have hXS : ∀ ω, logPrice σ c B t ω ≤ runMax σ c B t ω :=
    fun ω => le_runMax hcont σ c t ω ⟨zero_le, le_rfl⟩
  calc ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => g (logPrice σ c B t ω)) ω ∂P
      = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => f (logPrice σ c B t ω - a)) ω ∂P := by
        refine lintegral_congr (fun ω => ?_)
        by_cases h1 : a ≤ runMax σ c B t ω <;> by_cases h2 : logPrice σ c B t ω ≤ a <;>
          simp [Set.indicator, f, h1, h2, sub_nonpos]
    _ = ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω}
          (fun ω => f' (logPrice σ c B t ω - a)) ω ∂P :=
        RSMaxTermR1.R1pair hB hcont c σ hσ t ht a ha f f' hfm hf'm (C + C')
          (ENNReal.add_ne_top.2 ⟨hC, hC'⟩) hfC2 hf'C2 hfc hf'c hF
    _ = _ := by
        refine lintegral_congr (fun ω => ?_)
        by_cases h1 : a ≤ logPrice σ c B t ω
        · have h2 : a ≤ runMax σ c B t ω := h1.trans (hXS ω)
          have h3 : 0 ≤ logPrice σ c B t ω - a := sub_nonneg.2 h1
          simp only [Set.indicator, Set.mem_setOf_eq, f', Set.mem_Ici, h1, h2, h3, if_true]
          rw [show a - (logPrice σ c B t ω - a) = 2 * a - logPrice σ c B t ω by ring,
            show -κ * (logPrice σ c B t ω - a) = 2 * c * (a - logPrice σ c B t ω) / σ ^ 2 by
              rw [hκ]; ring]
        · have h3 : ¬ 0 ≤ logPrice σ c B t ω - a := by rw [sub_nonneg]; exact h1
          by_cases h2 : a ≤ runMax σ c B t ω <;> simp [Set.indicator, f', h1, h2, h3]


open RogersSatchell.Unbiased in
/-- Child `R` for the specific test function `g y = (2a - y)⁺`, by monotone truncation of `R_K`. -/
theorem R_spec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 < σ) (t : ℝ≥0) (ht : t ≠ 0) (a : ℝ) (ha : 0 < a) :
    ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => ENNReal.ofReal (2 * a - logPrice σ c B t ω)) ω ∂P =
      ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => ENNReal.ofReal (2 * a - (2 * a - logPrice σ c B t ω)) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P := by
  let cl : ℕ → ℝ → ℝ := fun m y => max 0 (min 1 (y + m))
  let gm : ℕ → ℝ → ENNReal := fun m y => ENNReal.ofReal ((2 * a - y) * cl m y)
  have hcl0 : ∀ m y, 0 ≤ cl m y := fun m y => le_max_left _ _
  have hcl1 : ∀ m y, cl m y ≤ 1 := fun m y => max_le zero_le_one (min_le_left _ _)
  have hclmono : ∀ y, Monotone fun m => cl m y := fun y m m' hmm' =>
    max_le_max le_rfl (min_le_min le_rfl (by have h := (Nat.cast_le (α := ℝ)).2 hmm'; linarith))
  have hgmc : ∀ m, Continuous (gm m) := fun m => ENNReal.continuous_ofReal.comp
    ((continuous_const.sub continuous_id).mul
      (continuous_const.max (continuous_const.min (continuous_id.add continuous_const))))
  have hgmC : ∀ (m : ℕ) (y : ℝ), gm m y ≤ ENNReal.ofReal (2 * a + m) := fun m y => by
    apply ENNReal.ofReal_le_ofReal
    have h0 := hcl0 m y
    have h1 := hcl1 m y
    by_cases hy : y + m ≤ 0
    · have : cl m y = 0 := by
        show max 0 (min 1 (y + m)) = 0
        exact max_eq_left (min_le_of_right_le hy)
      rw [this, mul_zero]; positivity
    · push_neg at hy
      have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
      by_cases h2 : 0 ≤ 2 * a - y
      · have := mul_le_mul_of_nonneg_left h1 h2; nlinarith
      · have := mul_le_mul_of_nonneg_right (le_of_lt (not_le.1 h2)) h0; nlinarith
  have hgmM : ∀ (m : ℕ) (y : ℝ), y ≤ -(m:ℝ) → gm m y = 0 := fun m y hy => by
    have : cl m y = 0 := by
      show max 0 (min 1 (y + m)) = 0
      exact max_eq_left (min_le_of_right_le (by linarith))
    show ENNReal.ofReal ((2 * a - y) * cl m y) = 0
    rw [this, mul_zero, ENNReal.ofReal_zero]
  have hgm_ev : ∀ (y : ℝ) (m : ℕ), -y + 1 ≤ (m : ℝ) → gm m y = ENNReal.ofReal (2 * a - y) := fun y m hm => by
    have : cl m y = 1 := by
      show max 0 (min 1 (y + m)) = 1
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    show ENNReal.ofReal ((2 * a - y) * cl m y) = _
    rw [this, mul_one]
  have hgm_mono : ∀ y : ℝ, Monotone fun m => gm m y := fun y m m' hmm' => by
    show ENNReal.ofReal ((2 * a - y) * cl m y) ≤ ENNReal.ofReal ((2 * a - y) * cl m' y)
    by_cases h2 : 0 ≤ 2 * a - y
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hclmono y hmm') h2)
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_iff.2 (Or.inr ⟨(not_le.1 h2).le, hcl0 m y⟩))]
      exact bot_le
  have hgm_t : ∀ y : ℝ, Tendsto (fun m => gm m y) atTop (𝓝 (ENNReal.ofReal (2 * a - y))) := fun y => by
    obtain ⟨m0, hm0⟩ := exists_nat_ge (-y + 1)
    exact tendsto_atTop_of_eventually_const (i₀ := m0) (fun m hm =>
      hgm_ev y m (hm0.trans (Nat.cast_le.2 hm)))
  have hK : ∀ m : ℕ, ∫⁻ ω, Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => gm m (logPrice σ c B t ω)) ω ∂P =
      ∫⁻ ω, Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => gm m (2 * a - logPrice σ c B t ω) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω ∂P :=
    fun m => R_K hB hcont c σ hσ t ht a ha (gm m) (hgmc m) _ ENNReal.ofReal_ne_top (hgmC m) m
      (hgmM m)
  have hXm := (hasLaw_logPrice hB c σ t).aemeasurable
  have hSm := aemeasurable_runMax hB hcont σ c t
  have hS1 : NullMeasurableSet {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a} P :=
    (nullMeasurableSet_le aemeasurable_const hSm).inter (nullMeasurableSet_le hXm aemeasurable_const)
  have hS2 : NullMeasurableSet {ω | a ≤ logPrice σ c B t ω} P :=
    nullMeasurableSet_le aemeasurable_const hXm
  have hL := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun m ω => Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => gm m (logPrice σ c B t ω)) ω)
    (F := fun ω => Set.indicator {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
        (fun ω => ENNReal.ofReal (2 * a - logPrice σ c B t ω)) ω) (μ := P)
    (fun m => ((hgmc m).measurable.comp_aemeasurable hXm).indicator₀ hS1)
    (ae_of_all _ (fun ω m m' hmm' => by
      by_cases h : ω ∈ {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
      · simp only [Set.indicator_of_mem h]; exact hgm_mono _ hmm'
      · simp only [Set.indicator_of_notMem h]; exact le_rfl))
    (ae_of_all _ (fun ω => by
      by_cases h : ω ∈ {ω | a ≤ runMax σ c B t ω ∧ logPrice σ c B t ω ≤ a}
      · simp only [Set.indicator_of_mem h]; exact hgm_t _
      · simp only [Set.indicator_of_notMem h]; exact tendsto_const_nhds))
  have hR := lintegral_tendsto_of_tendsto_of_monotone
    (f := fun m ω => Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => gm m (2 * a - logPrice σ c B t ω) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω)
    (F := fun ω => Set.indicator {ω | a ≤ logPrice σ c B t ω}
        (fun ω => ENNReal.ofReal (2 * a - (2 * a - logPrice σ c B t ω)) *
          ENNReal.ofReal (Real.exp (2 * c * (a - logPrice σ c B t ω) / σ ^ 2))) ω) (μ := P)
    (fun m => (((hgmc m).measurable.comp_aemeasurable (aemeasurable_const.sub hXm)).mul
      ((by fun_prop : Measurable fun x : ℝ =>
        ENNReal.ofReal (Real.exp (2 * c * (a - x) / σ ^ 2))).comp_aemeasurable hXm)).indicator₀ hS2)
    (ae_of_all _ (fun ω m m' hmm' => by
      by_cases h : ω ∈ {ω | a ≤ logPrice σ c B t ω}
      · simp only [Set.indicator_of_mem h]; exact mul_le_mul' (hgm_mono _ hmm') le_rfl
      · simp only [Set.indicator_of_notMem h]; exact le_rfl))
    (ae_of_all _ (fun ω => by
      by_cases h : ω ∈ {ω | a ≤ logPrice σ c B t ω}
      · simp only [Set.indicator_of_mem h]
        exact ENNReal.Tendsto.mul_const (hgm_t _) (Or.inr ENNReal.ofReal_ne_top)
      · simp only [Set.indicator_of_notMem h]; exact tendsto_const_nhds))
  exact tendsto_nhds_unique (hL.congr (fun m => hK m)) hR

end RSMaxTerm

open MeasureTheory ProbabilityTheory NNReal RogersSatchell.Unbiased in
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcont : ∀ ω, Continuous fun t => B t ω)
    (c σ : ℝ) (hσ : 0 ≤ σ) (t : ℝ≥0) :
    Integrable (fun ω => runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω)) P ∧
    ∫ ω, runMax σ c B t ω * (runMax σ c B t ω - logPrice σ c B t ω) ∂P = σ ^ 2 * t / 2 := by
  exact RSMaxTerm.parent_of_R hB hcont c σ hσ t
    (fun hσp ht a ha => RSMaxTerm.R_spec hB hcont c σ hσp t ht a ha)
