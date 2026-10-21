-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P39.coherent_distribution_comparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T17:40:10.310862+00:00
-- url     : https://prove2.me/submissions/905aaf9b-7890-4e4b-96f7-413d4866d33c

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Next46 QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixBorel

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

variable (R : FiniteModel G I S)

variable {R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

section G62jGauss
open MeasureTheory

lemma g62j_prod_int (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun z : ℂ => f z.re * g z.im) ∧
      ∫ z : ℂ, f z.re * g z.im = (∫ x, f x) * (∫ y, g y) := by
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := (Complex.measurableEquivRealProd.symm).measurableEmbedding
  have hprod : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2) := by
    rw [Measure.volume_eq_prod]; exact hf.mul_prod hg
  constructor
  · have := (hmp.integrable_comp_emb hemb (g := fun z : ℂ => f z.re * g z.im)).mp
    exact this hprod
  · have := hmp.integral_comp hemb (fun z : ℂ => f z.re * g z.im)
    rw [← this]
    change ∫ p : ℝ × ℝ, f p.1 * g p.2 = _
    rw [Measure.volume_eq_prod, integral_prod_mul]

lemma g62j_G2 {c : ℝ} (hc : 0 < c) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-c * x ^ 2) = Real.sqrt (Real.pi / c) / (2 * c) := by
  have h1 : ∫ x : ℝ, x ^ 2 * Real.exp (-c * x ^ 2) =
      ∫ x : ℝ, (fun t : ℝ => t ^ 2 * Real.exp (-c * t ^ 2)) |x| := by
    congr 1; funext x; simp [sq_abs]
  rw [h1, integral_comp_abs (f := fun t : ℝ => t ^ 2 * Real.exp (-c * t ^ 2))]
  have h2 : ∫ x in Set.Ioi (0 : ℝ), x ^ 2 * Real.exp (-c * x ^ 2) =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (2 : ℝ) * Real.exp (-c * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [Real.rpow_two]
  rw [h2, integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hc]
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt Real.pi / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG]
  have hc' : c ^ (-(2 + 1 : ℝ) / 2) = (c * Real.sqrt c)⁻¹ := by
    rw [show (-(2 + 1 : ℝ) / 2) = -(1 + 1 / 2) by norm_num, Real.rpow_neg hc.le,
      Real.rpow_add hc, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hc', Real.sqrt_div' _ hc.le]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  field_simp

lemma g62j_I2 {c : ℝ} (hc : 0 < c) : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-c * x ^ 2)) := by
  have := integrable_rpow_mul_exp_neg_mul_sq hc (s := 2) (by norm_num)
  refine this.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only
  rw [Real.rpow_two]

end G62jGauss

section G62jGauss2
open MeasureTheory

lemma g62j_odd {c : ℝ} (hc : 0 < c) : ∫ x : ℝ, x * Real.exp (-c * x ^ 2) = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => x * Real.exp (-c * x ^ 2)) volume
  simp only [neg_mul, neg_sq, integral_neg] at h ⊢
  linarith

lemma g62j_split (k : ℝ) (w : ℂ) :
    Real.exp (-k * Complex.normSq w) = Real.exp (-k * w.re ^ 2) * Real.exp (-k * w.im ^ 2) := by
  rw [← Real.exp_add, Complex.normSq_apply]; congr 1; ring

lemma g62j_centered {k : ℝ} (hk : 0 < k) :
    Integrable (fun w : ℂ => k * Real.exp (-k * Complex.normSq w)) ∧
    ∫ w : ℂ, k * Real.exp (-k * Complex.normSq w) = k * (Real.pi / k) ∧
    Integrable (fun w : ℂ => w.re ^ 2 * (k * Real.exp (-k * Complex.normSq w))) ∧
    ∫ w : ℂ, w.re ^ 2 * (k * Real.exp (-k * Complex.normSq w)) = k * (Real.pi / (2 * k ^ 2)) ∧
    Integrable (fun w : ℂ => w.im ^ 2 * (k * Real.exp (-k * Complex.normSq w))) ∧
    ∫ w : ℂ, w.im ^ 2 * (k * Real.exp (-k * Complex.normSq w)) = k * (Real.pi / (2 * k ^ 2)) ∧
    Integrable (fun w : ℂ => w.re * (k * Real.exp (-k * Complex.normSq w))) ∧
    ∫ w : ℂ, w.re * (k * Real.exp (-k * Complex.normSq w)) = 0 ∧
    Integrable (fun w : ℂ => w.im * (k * Real.exp (-k * Complex.normSq w))) ∧
    ∫ w : ℂ, w.im * (k * Real.exp (-k * Complex.normSq w)) = 0 := by
  have I0 := integrable_exp_neg_mul_sq hk
  have I1 := integrable_mul_exp_neg_mul_sq hk
  have I2 := g62j_I2 hk
  have G0 := integral_gaussian k
  have G1 := g62j_odd hk
  have G2 := g62j_G2 hk
  have P00 := g62j_prod_int _ _ I0 I0
  have P20 := g62j_prod_int _ _ I2 I0
  have P02 := g62j_prod_int _ _ I0 I2
  have P10 := g62j_prod_int _ _ I1 I0
  have P01 := g62j_prod_int _ _ I0 I1
  have hpk : Real.sqrt (Real.pi / k) * Real.sqrt (Real.pi / k) = Real.pi / k :=
    Real.mul_self_sqrt (by positivity)
  have e0 : (fun w : ℂ => k * Real.exp (-k * Complex.normSq w)) =
      fun w => k * (Real.exp (-k * w.re ^ 2) * Real.exp (-k * w.im ^ 2)) := by
    funext w; rw [g62j_split]
  have e20 : (fun w : ℂ => w.re ^ 2 * (k * Real.exp (-k * Complex.normSq w))) =
      fun w => k * (w.re ^ 2 * Real.exp (-k * w.re ^ 2) * Real.exp (-k * w.im ^ 2)) := by
    funext w; rw [g62j_split]; ring
  have e02 : (fun w : ℂ => w.im ^ 2 * (k * Real.exp (-k * Complex.normSq w))) =
      fun w => k * (Real.exp (-k * w.re ^ 2) * (w.im ^ 2 * Real.exp (-k * w.im ^ 2))) := by
    funext w; rw [g62j_split]; ring
  have e10 : (fun w : ℂ => w.re * (k * Real.exp (-k * Complex.normSq w))) =
      fun w => k * (w.re * Real.exp (-k * w.re ^ 2) * Real.exp (-k * w.im ^ 2)) := by
    funext w; rw [g62j_split]; ring
  have e01 : (fun w : ℂ => w.im * (k * Real.exp (-k * Complex.normSq w))) =
      fun w => k * (Real.exp (-k * w.re ^ 2) * (w.im * Real.exp (-k * w.im ^ 2))) := by
    funext w; rw [g62j_split]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact P00.1.const_mul k
  · rw [e0, integral_const_mul, P00.2, G0, hpk]
  · rw [e20]; exact P20.1.const_mul k
  · rw [e20, integral_const_mul, P20.2, G2, G0]
    rw [show Real.sqrt (Real.pi / k) / (2 * k) * Real.sqrt (Real.pi / k) =
      (Real.sqrt (Real.pi / k) * Real.sqrt (Real.pi / k)) / (2 * k) by ring, hpk]
    field_simp
  · rw [e02]; exact P02.1.const_mul k
  · rw [e02, integral_const_mul, P02.2, G2, G0]
    rw [show Real.sqrt (Real.pi / k) * (Real.sqrt (Real.pi / k) / (2 * k)) =
      (Real.sqrt (Real.pi / k) * Real.sqrt (Real.pi / k)) / (2 * k) by ring, hpk]
    field_simp
  · rw [e10]; exact P10.1.const_mul k
  · rw [e10, integral_const_mul, P10.2, G1]; simp
  · rw [e01]; exact P01.1.const_mul k
  · rw [e01, integral_const_mul, P01.2, G1]; simp

end G62jGauss2

section G62jGauss3
open MeasureTheory

lemma g62j_main {k : ℝ} (hk : 0 < k) (a : ℂ) :
      Integrable (displacementDensity k a) phaseMeasure ∧
      (∫ z, displacementDensity k a z ∂phaseMeasure) = 1 ∧
      Integrable (fun z => (z - a) * (displacementDensity k a z : ℂ)) phaseMeasure ∧
      (∫ z, (z - a) * (displacementDensity k a z : ℂ) ∂phaseMeasure) = 0 ∧
      Integrable (fun z => Complex.normSq (z - a) * displacementDensity k a z) phaseMeasure ∧
      (∫ z, Complex.normSq (z - a) * displacementDensity k a z ∂phaseMeasure) = k⁻¹ ∧
      Integrable (fun z => (z - a).re ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).re ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹ ∧
      Integrable (fun z => (z - a).im ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).im ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹ := by
  obtain ⟨I0, G0, I20, G20, I02, G02, I10, G10, I01, G01⟩ := g62j_centered hk
  set F : ℂ → ℝ := fun w => k * Real.exp (-k * Complex.normSq w) with hF
  have hc : ENNReal.ofReal Real.pi⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpi : (ENNReal.ofReal Real.pi⁻¹).toReal = Real.pi⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.pi_pos.le)
  have hsm : ∀ f : ℂ → ℝ, ∫ z, f z ∂phaseMeasure = Real.pi⁻¹ * ∫ z, f z := by
    intro f; rw [phaseMeasure, integral_smul_measure, hpi, smul_eq_mul]
  have hsmC : ∀ f : ℂ → ℂ, ∫ z, f z ∂phaseMeasure = (Real.pi⁻¹ : ℝ) • ∫ z, f z := by
    intro f; rw [phaseMeasure, integral_smul_measure, hpi]
  have hint : ∀ {β : Type} [NormedAddCommGroup β] (f : ℂ → β), Integrable f →
      Integrable (fun z => f (z - a)) phaseMeasure := by
    intro β _ f hf; rw [phaseMeasure]; exact (hf.comp_sub_right a).smul_measure hc
  have hD : displacementDensity k a = fun z => F (z - a) := rfl
  have IN : Integrable (fun w : ℂ => Complex.normSq w * F w) := by
    have := I20.add I02
    refine this.congr (Filter.Eventually.of_forall (fun w => ?_))
    simp only [Pi.add_apply, hF, Complex.normSq_apply]; ring
  have GN : ∫ w : ℂ, Complex.normSq w * F w = k * (Real.pi / (2 * k ^ 2)) + k * (Real.pi / (2 * k ^ 2)) := by
    have : ∫ w : ℂ, Complex.normSq w * F w = ∫ w : ℂ, (w.re ^ 2 * F w + w.im ^ 2 * F w) := by
      congr 1; funext w; simp only [Complex.normSq_apply]; ring
    rw [this, integral_add I20 I02, G20, G02]
  have I10' : Integrable (fun w : ℂ => w.re * F w) := I10
  have I01' : Integrable (fun w : ℂ => w.im * F w) := I01
  have G10' : ∫ w : ℂ, w.re * F w = 0 := G10
  have G01' : ∫ w : ℂ, w.im * F w = 0 := G01
  have e : (fun w : ℂ => w * (F w : ℂ)) = fun w =>
      ((w.re * F w : ℝ) : ℂ) + Complex.I * ((w.im * F w : ℝ) : ℂ) := by
    funext w; apply Complex.ext <;> simp <;> ring
  have IC : Integrable (fun w : ℂ => w * (F w : ℂ)) := by
    rw [e]; exact I10'.ofReal.add (I01'.ofReal.const_mul Complex.I)
  have GC : ∫ w : ℂ, w * (F w : ℂ) = 0 := by
    rw [e, integral_add, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      G10', G01']
    · simp
    · exact I10'.ofReal
    · exact I01'.ofReal.const_mul Complex.I
  have tr : ∀ Y : ℂ → ℝ, ∫ z, Y (z - a) ∂phaseMeasure = Real.pi⁻¹ * ∫ w, Y w := by
    intro Y
    rw [phaseMeasure, integral_smul_measure, hpi, smul_eq_mul, integral_sub_right_eq_self Y a]
  have trC : ∀ Y : ℂ → ℂ, ∫ z, Y (z - a) ∂phaseMeasure = (Real.pi⁻¹ : ℝ) • ∫ w, Y w := by
    intro Y
    rw [phaseMeasure, integral_smul_measure, hpi, integral_sub_right_eq_self Y a]
  have hpi0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hint F I0
  · rw [show (∫ z, displacementDensity k a z ∂phaseMeasure) = Real.pi⁻¹ * ∫ w, F w from tr F, G0]
    field_simp
  · exact hint (fun w : ℂ => w * (F w : ℂ)) IC
  · rw [show (∫ z, (z - a) * (displacementDensity k a z : ℂ) ∂phaseMeasure) =
      (Real.pi⁻¹ : ℝ) • ∫ w, w * (F w : ℂ) from trC (fun w : ℂ => w * (F w : ℂ)), GC, smul_zero]
  · exact hint (fun w : ℂ => Complex.normSq w * F w) IN
  · rw [show (∫ z, Complex.normSq (z - a) * displacementDensity k a z ∂phaseMeasure) =
      Real.pi⁻¹ * ∫ w, Complex.normSq w * F w from tr (fun w : ℂ => Complex.normSq w * F w), GN]
    field_simp; ring
  · exact hint (fun w : ℂ => w.re ^ 2 * F w) I20
  · rw [show (∫ z, (z - a).re ^ 2 * displacementDensity k a z ∂phaseMeasure) =
      Real.pi⁻¹ * ∫ w, w.re ^ 2 * F w from tr (fun w : ℂ => w.re ^ 2 * F w), G20]
    field_simp
  · exact hint (fun w : ℂ => w.im ^ 2 * F w) I02
  · rw [show (∫ z, (z - a).im ^ 2 * displacementDensity k a z ∂phaseMeasure) =
      Real.pi⁻¹ * ∫ w, w.im ^ 2 * F w from tr (fun w : ℂ => w.im ^ 2 * F w), G02]
    field_simp

end G62jGauss3

/-- PDF pp.18–19: statistical comparison of the explicit laws (43),(55).
Complex mean squared error and each individual quadrature variance both
fall by a factor two; the likelihood density doubles. -/
theorem solution (a : ℂ) :
    (∀ k ∈ ({2, 4} : Set ℝ),
      Integrable (displacementDensity k a) phaseMeasure ∧
      (∫ z, displacementDensity k a z ∂phaseMeasure) = 1 ∧
      Integrable (fun z => (z - a) * (displacementDensity k a z : ℂ)) phaseMeasure ∧
      (∫ z, (z - a) * (displacementDensity k a z : ℂ) ∂phaseMeasure) = 0 ∧
      Integrable (fun z => Complex.normSq (z - a) * displacementDensity k a z) phaseMeasure ∧
      (∫ z, Complex.normSq (z - a) * displacementDensity k a z ∂phaseMeasure) = k⁻¹ ∧
      Integrable (fun z => (z - a).re ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).re ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹ ∧
      Integrable (fun z => (z - a).im ^ 2 * displacementDensity k a z) phaseMeasure ∧
      (∫ z, (z - a).im ^ 2 * displacementDensity k a z ∂phaseMeasure) = (2*k)⁻¹) ∧
    displacementDensity 4 a a = 2 * displacementDensity 2 a a ∧
    (∫ z, Complex.normSq (z - a) * displacementDensity 4 a z ∂phaseMeasure) =
      (1/2 : ℝ) * ∫ z, Complex.normSq (z - a) * displacementDensity 2 a z ∂phaseMeasure := by
  have hall : ∀ k ∈ ({2, 4} : Set ℝ), 0 < k := by
    intro k hk
    rcases hk with rfl | hk
    · norm_num
    · rw [Set.mem_singleton_iff] at hk; rw [hk]; norm_num
  refine ⟨fun k hk => g62j_main (hall k hk) a, ?_, ?_⟩
  · simp [displacementDensity]; norm_num
  · rw [(g62j_main (by norm_num : (0 : ℝ) < 4) a).2.2.2.2.2.1,
      (g62j_main (by norm_num : (0 : ℝ) < 2) a).2.2.2.2.2.1]
    norm_num



end
