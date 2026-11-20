-- Prove2me | solution 1 for UniversalSubmod.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T10:10:07.362747+00:00
-- url     : https://prove2.me/submissions/ba31bc4e-75e9-4d3f-be4a-169fd2b48af5

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_NonmonotoneSubmod_Shared_OPT
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_UniversalSubmod_threshSet
import Definitions.Def_UniversalSubmod_CorrMatrix
import Definitions.Def_UniversalSubmod_semidefExt
import Definitions.Def_Cohen2019_Robust_Phi
import Theorems.Thm_UniversalSubmod_theorem_2_3
import Theorems.Thm_UniversalSubmod_lemma_2_1

section
set_option autoImplicit false

namespace UniversalSubmod.Dev.Thm24

open MeasureTheory ProbabilityTheory Cohen2019.Robust NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

lemma meas_comp {α : Type*} [MeasurableSpace α] {n : ℕ} (φ : α → Finset (Fin n))
    (hφ : ∀ i, MeasurableSet {a | i ∈ φ a}) (f : Finset (Fin n) → ℝ) :
    Measurable (fun a => f (φ a)) := by
  classical
  have h : (fun a => f (φ a)) = fun a => ∑ S : Finset (Fin n), if φ a = S then f S else 0 := by
    funext a
    rw [Finset.sum_eq_single (φ a)]
    · simp
    · intro S _ hS; simp [Ne.symm hS]
    · simp
  rw [h]
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {a | φ a = S} = ⋂ i, {a | i ∈ φ a ↔ i ∈ S} := by
    ext a; simp [Finset.ext_iff]
  rw [this]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · simpa [hi] using hφ i
  · have e : {a | i ∈ φ a ↔ i ∈ S} = {a | i ∈ φ a}ᶜ := by ext a; simp [hi]
    rw [e]; exact (hφ i).compl

lemma integrable_bdd {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Measurable g) (C : ℝ) (h : ∀ a, |g a| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C
    (ae_of_all _ (fun a => by simpa [Real.norm_eq_abs] using h a))

lemma gauss_Iic (u : ℝ) : (gaussianReal 0 1).real (Set.Iic u) = Phi u := by
  unfold Phi; rw [cdf_eq_real]

lemma phi_nonneg (u : ℝ) : 0 ≤ Phi u := by unfold Phi; exact cdf_nonneg _ _
lemma phi_le_one (u : ℝ) : Phi u ≤ 1 := by unfold Phi; exact cdf_le_one _ _

lemma gauss_singleton (x : ℝ) : gaussianReal 0 1 {x} = 0 :=
  gaussianReal_absolutelyContinuous 0 one_ne_zero (by simp)

lemma gauss_Iio_ae (u : ℝ) : Set.Iio u =ᵐ[gaussianReal 0 1] Set.Iic u :=
  Iio_ae_eq_Iic' (gauss_singleton u)

lemma gauss_Ioc (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Set.Ioc a b) = Phi b - Phi a := by
  have : Set.Iic b \ Set.Iic a = Set.Ioc a b := by
    ext x; simp [Set.mem_Ioc, and_comm]
  rw [← this, measureReal_sdiff (Set.Iic_subset_Iic.2 hab) measurableSet_Iic,
    gauss_Iic, gauss_Iic]

lemma phi_strictMono : StrictMono Phi := by
  intro a b hab
  have h1 : 0 < (gaussianReal 0 1).real (Set.Ioc a b) := by
    have h2 : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
      intro h
      have := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) one_ne_zero h
      simp at this
      linarith
    exact ENNReal.toReal_pos h2 (measure_ne_top _ _)
  rw [gauss_Ioc a b hab.le] at h1
  linarith

lemma phi_le_iff (a b : ℝ) : Phi a ≤ Phi b ↔ a ≤ b := phi_strictMono.le_iff_le

lemma gauss_Iio (u : ℝ) : (gaussianReal 0 1).real (Set.Iio u) = Phi u := by
  rw [← gauss_Iic]; exact measureReal_congr (gauss_Iio_ae u)

lemma gauss_Ici (u : ℝ) : (gaussianReal 0 1).real (Set.Ici u) = 1 - Phi u := by
  rw [← gauss_Iio, ← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ]

lemma phi_zero : Phi 0 = 1 / 2 := by
  have h2 : gaussianReal 0 1 (Set.Iic 0) = gaussianReal 0 1 (Set.Ici 0) := by
    have := gaussianReal_map_neg (μ := 0) (v := 1)
    rw [neg_zero] at this
    conv_lhs => rw [← this]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1; ext x; simp
  have h : (gaussianReal 0 1).real (Set.Iic 0) = (gaussianReal 0 1).real (Set.Ici 0) := by
    simp [Measure.real, h2]
  rw [gauss_Iic, gauss_Ici] at h
  linarith

lemma phi_sq_bound (u : ℝ) : (Phi u - 1 / 2) ^ 2 ≤ u ^ 2 / (2 * Real.pi) := by
  have hc : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hdens : ∀ x : ℝ, ‖gaussianPDFReal 0 1 x‖ ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro x
    have hh : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) hh
  have key : ∀ a b : ℝ, a ≤ b → Phi b - Phi a ≤ (b - a) * (Real.sqrt (2 * Real.pi))⁻¹ := by
    intro a b hab
    rw [← gauss_Ioc a b hab, Measure.real, gaussianReal_apply_eq_integral 0 one_ne_zero _,
      ENNReal.toReal_ofReal]
    · have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc a b)
        (f := gaussianPDFReal 0 1) (C := (Real.sqrt (2 * Real.pi))⁻¹)
        (by simp) (fun x _ => hdens x)
      rw [Real.norm_eq_abs, Real.volume_real_Ioc_of_le hab] at this
      linarith [le_abs_self (∫ x in Set.Ioc a b, gaussianPDFReal 0 1 x)]
    · exact setIntegral_nonneg measurableSet_Ioc (fun x _ => gaussianPDFReal_nonneg _ _ _)
  have hb : |Phi u - 1 / 2| ≤ |u| * (Real.sqrt (2 * Real.pi))⁻¹ := by
    rcases le_total 0 u with h | h
    · have k := key 0 u h
      have m := phi_strictMono.monotone h
      rw [phi_zero] at k m
      rw [abs_of_nonneg (by linarith), abs_of_nonneg h]
      linarith
    · have k := key u 0 h
      have m := phi_strictMono.monotone h
      rw [phi_zero] at k m
      rw [abs_of_nonpos (by linarith), abs_of_nonpos h]
      linarith
  calc (Phi u - 1/2)^2 = |Phi u - 1/2|^2 := (sq_abs _).symm
    _ ≤ (|u| * (Real.sqrt (2 * Real.pi))⁻¹)^2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
    _ = u^2 / (2 * Real.pi) := by
      rw [mul_pow, sq_abs, inv_pow, Real.sq_sqrt (by positivity)]; ring


lemma pi_integral_filter {n : ℕ} (f : Finset (Fin n) → ℝ) (u : ℝ) :
    ∫ y : Fin n → ℝ, f (Finset.univ.filter (fun i => u ≤ y i))
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) = F f (fun _ => 1 - Phi u) := by
  classical
  let φ : Finset (Fin n) → (Fin n → ℝ) → ℝ := fun S y =>
    ∏ i : Fin n, (if i ∈ S then (Set.Ici u).indicator (fun _ => (1:ℝ)) (y i)
      else (Set.Iio u).indicator (fun _ => (1:ℝ)) (y i))
  have key : ∀ y : Fin n → ℝ, f (Finset.univ.filter (fun i => u ≤ y i)) =
      ∑ S : Finset (Fin n), f S * φ S y := by
    intro y
    rw [Finset.sum_eq_single (Finset.univ.filter (fun i => u ≤ y i))]
    · have : φ (Finset.univ.filter (fun i => u ≤ y i)) y = 1 :=
        Finset.prod_eq_one (fun i _ => by by_cases h : u ≤ y i <;> simp [h])
      rw [this, mul_one]
    · intro S _ hS
      have : φ S y = 0 := by
        obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ Finset.univ.filter (fun i => u ≤ y i)) := by
          by_contra h; push Not at h; exact hS (Finset.ext h)
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        by_cases h1 : i ∈ S <;> by_cases h2 : u ≤ y i <;> simp_all
      rw [this, mul_zero]
    · simp
  have hmeas : ∀ S, Measurable (φ S) := by
    intro S
    refine Finset.measurable_prod _ (fun i _ => ?_)
    by_cases h : i ∈ S
    · simp only [h, if_true]
      exact (measurable_const.indicator measurableSet_Ici).comp (measurable_pi_apply i)
    · simp only [h, if_false]
      exact (measurable_const.indicator measurableSet_Iio).comp (measurable_pi_apply i)
  have hbound : ∀ S y, |φ S y| ≤ 1 := by
    intro S y
    simp only [φ, Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs <;> simp [Set.indicator_apply] <;> split_ifs <;> simp
  simp_rw [key]
  rw [integral_finsetSum]
  · unfold F
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [integral_const_mul]
    congr 1
    have := integral_fintype_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
      (fun (i : Fin n) (x : ℝ) => if i ∈ S then (Set.Ici u).indicator (fun _ => (1:ℝ)) x
        else (Set.Iio u).indicator (fun _ => (1:ℝ)) x)
    refine this.trans (Finset.prod_congr rfl (fun i _ => ?_))
    by_cases h : i ∈ S
    · simp only [h, if_true]
      rw [integral_indicator_const _ measurableSet_Ici, gauss_Ici]; simp
    · simp only [h, if_false]
      rw [integral_indicator_const _ measurableSet_Iio, gauss_Iio]; simp
  · intro S _
    exact (integrable_bdd _ (hmeas S) 1 (hbound S)).const_mul _


def Sc {n : ℕ} (a b : ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => (if i = j then a^2 else 0) + b^2

lemma Sc_quad {n : ℕ} (a b : ℝ) (x : Fin n → ℝ) :
    dotProduct x (Matrix.mulVec (Sc a b) x) = a^2 * ∑ i, x i ^ 2 + b^2 * (∑ i, x i)^2 := by
  simp only [Sc, dotProduct, Matrix.mulVec, Matrix.of_apply, add_mul, Finset.sum_add_distrib,
    mul_add, Finset.mul_sum, Finset.sum_mul, ite_mul, zero_mul, mul_ite, mul_zero]
  simp [sq, Finset.sum_ite_eq, mul_comm, mul_left_comm, mul_assoc, Finset.mul_sum, Finset.sum_mul]

lemma Sc_psd {n : ℕ} (a b : ℝ) : (Sc (n := n) a b).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · ext i j; simp [Sc, Matrix.conjTranspose_apply, eq_comm]
  · simpa [Sc_quad] using by positivity

lemma law_gram {m n : ℕ} (w : Fin n → EuclideanSpace ℝ (Fin m)) :
    (stdGaussian (EuclideanSpace ℝ (Fin m))).map
      (fun z => (WithLp.toLp 2 (fun i => ⟪w i, z⟫) : EuclideanSpace ℝ (Fin n)))
      = multivariateGaussian 0 (Matrix.gram ℝ w) := by
  have hS := Matrix.posSemidef_gram ℝ w
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian hS, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ z : EuclideanSpace ℝ (Fin m),
      ⟪(WithLp.toLp 2 (fun i => ⟪w i, z⟫) : EuclideanSpace ℝ (Fin n)), t⟫ = ⟪z, ∑ i, t i • w i⟫ := by
    intro z
    rw [PiLp.inner_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [WithLp.ofLp_toLp]
    rw [inner_smul_right, real_inner_comm z (w i)]
    simp [mul_comm]
  simp_rw [h1]
  rw [← charFun_apply, charFun_stdGaussian]
  have h2 := Matrix.star_dotProduct_gram_mulVec (𝕜 := ℝ) w t.ofLp t.ofLp
  simp only [star_trivial, real_inner_self_eq_norm_sq] at h2
  rw [h2, inner_zero_right]
  push_cast
  congr 1
  ring

lemma law_corr {n : ℕ} (a b : ℝ) :
    ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)).map
      (fun p : ℝ × (Fin n → ℝ) =>
        (WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)))
      = multivariateGaussian 0 (Sc a b) := by
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_multivariateGaussian (Sc_psd a b), charFun_apply,
    integral_map (by fun_prop) (by fun_prop)]
  have h1 : ∀ p : ℝ × (Fin n → ℝ),
      Complex.exp (↑⟪(WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)), t⟫ * Complex.I)
      = Complex.exp (↑(b * (∑ i, t i) * p.1) * Complex.I) *
        ∏ i, Complex.exp (↑(a * t i * p.2 i) * Complex.I) := by
    intro p
    rw [← Complex.exp_sum, ← Complex.exp_add]
    congr 1
    rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← add_mul, ← Complex.ofReal_add]
    congr 2
    simp only [PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [h1]
  rw [integral_prod_mul (fun y0 : ℝ => Complex.exp (↑(b * (∑ i, t i) * y0) * Complex.I))
    (fun y : Fin n → ℝ => ∏ i, Complex.exp (↑(a * t i * y i) * Complex.I))]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
    (fun (i : Fin n) (x : ℝ) => Complex.exp (↑(a * t i * x) * Complex.I))]
  have e1 : ∀ (c : ℝ), ∫ y : ℝ, Complex.exp (↑(c * y) * Complex.I) ∂(gaussianReal 0 1)
      = Complex.exp (-(c ^ 2 : ℝ) / 2) := by
    intro c
    have := charFun_gaussianReal (μ := 0) (v := 1) c
    rw [charFun_apply_real] at this
    simp only [Complex.ofReal_mul] at this ⊢
    rw [this]
    simp
    ring_nf
  simp_rw [e1]
  rw [← Complex.exp_sum, ← Complex.exp_add, inner_zero_right, Sc_quad]
  congr 1
  push_cast
  simp only [zero_mul, zero_sub, mul_pow, neg_div, Finset.sum_neg_distrib, ← Finset.sum_div,
    ← Finset.mul_sum]
  ring

lemma f_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : |f S| ≤ ∑ T, |f T| :=
  Finset.single_le_sum (f := fun T => |f T|) (fun T _ => abs_nonneg _) (Finset.mem_univ S)

lemma phi_meas : Measurable Phi := phi_strictMono.monotone.measurable

lemma semidefExt_Sc {n : ℕ} (f : Finset (Fin n) → ℝ) (a b : ℝ) (ha : 0 < a) (t : ℝ) :
    semidefExt f (fun _ => 1 - Phi t) (Sc a b)
      = ∫ y0 : ℝ, F f (fun _ => 1 - Phi ((t - b * y0) / a)) ∂(gaussianReal 0 1) := by
  unfold semidefExt
  rw [← law_corr a b]
  have hg : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  have hm : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i)))) := by
    refine meas_comp (fun g : EuclideanSpace ℝ (Fin n) =>
      Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i))) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_const (phi_meas.comp (by fun_prop))
  rw [integral_map hg.aemeasurable hm.aestronglyMeasurable]
  have e : ∀ p : ℝ × (Fin n → ℝ),
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi
        ((WithLp.toLp 2 (fun i => a * p.2 i + b * p.1) : EuclideanSpace ℝ (Fin n)) i)))
      = f (Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i)) := by
    intro p
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_sub_cancel, phi_le_iff,
      WithLp.ofLp_toLp, div_le_iff₀ ha]
    constructor <;> intro h <;> nlinarith
  simp_rw [e]
  have hm2 : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      f (Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i))) := by
    refine meas_comp (fun p : ℝ × (Fin n → ℝ) =>
      Finset.univ.filter (fun i => (t - b * p.1) / a ≤ p.2 i)) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le (by fun_prop) (by fun_prop)
  rw [integral_prod _ (integrable_bdd _ hm2 _ (fun p => f_bdd f _))]
  simp_rw [pi_integral_filter]


lemma gauss_int_id : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl

lemma gauss_int_sq : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 1) := by
  have := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
  simpa using this

lemma gauss_mean : ∫ y : ℝ, y ∂(gaussianReal 0 1) = 0 := integral_id_gaussianReal

lemma gauss_second : ∫ y : ℝ, y ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (memLp_id_gaussianReal (μ := 0) (v := 1) 2).aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

lemma gauss_quad (a b t : ℝ) (ha : 0 < a) :
    ∫ y : ℝ, (1 / 4 - ((t - b * y) / a) ^ 2 / (2 * Real.pi)) ∂(gaussianReal 0 1)
      = 1 / 4 - (t ^ 2 + b ^ 2) / (a ^ 2 * (2 * Real.pi)) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have e : (fun y : ℝ => 1 / 4 - ((t - b * y) / a) ^ 2 / (2 * Real.pi)) =
      fun y => (1 / 4 - t ^ 2 / (a ^ 2 * (2 * Real.pi))) +
        (2 * t * b / (a ^ 2 * (2 * Real.pi))) * y - (b ^ 2 / (a ^ 2 * (2 * Real.pi))) * y ^ 2 := by
    funext y; field_simp; ring
  rw [e, integral_sub, integral_add, integral_const, integral_const_mul, integral_const_mul,
    gauss_mean, gauss_second]
  · simp; field_simp; ring
  · exact integrable_const _
  · exact gauss_int_id.const_mul _
  · exact (integrable_const _).add (gauss_int_id.const_mul _)
  · exact gauss_int_sq.const_mul _


lemma F_bdd {n : ℕ} (f : Finset (Fin n) → ℝ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    |F f (fun _ => p)| ≤ ∑ T, |f T| := by
  unfold F
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
  rw [abs_mul]
  have : |∏ i : Fin n, (if i ∈ S then p else 1 - p)| ≤ 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => ?_)
    split_ifs
    · rw [abs_of_nonneg hp0]; exact hp1
    · rw [abs_of_nonneg (by linarith)]; linarith
  calc |f S| * |∏ i : Fin n, (if i ∈ S then p else 1 - p)| ≤ |f S| * 1 :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = |f S| := mul_one _

lemma F_meas {n : ℕ} (f : Finset (Fin n) → ℝ) {α : Type*} [MeasurableSpace α] (q : α → ℝ)
    (hq : Measurable q) : Measurable (fun y => F f (fun _ => q y)) := by
  unfold F
  refine Finset.measurable_sum _ (fun S _ => ?_)
  refine Measurable.const_mul (Finset.measurable_prod _ (fun i _ => ?_)) _
  split_ifs
  · exact hq
  · exact measurable_const.sub hq

lemma OPT_nonneg {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) : 0 ≤ OPT f :=
  (hf0 ∅).trans (Finset.le_sup' f (Finset.mem_univ ∅))

lemma pointwise {n : ℕ} (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f)
    (a b t : ℝ) (ha : 0 < a) :
    OPT f * (1 / 4 - (t ^ 2 + b ^ 2) / (a ^ 2 * (2 * Real.pi)))
      ≤ semidefExt f (fun _ => 1 - Phi t) (Sc a b) := by
  rw [semidefExt_Sc f a b ha t]
  have hO := OPT_nonneg f hf0
  have h1 : ∀ y : ℝ, OPT f * (1 / 4 - ((t - b * y) / a) ^ 2 / (2 * Real.pi))
      ≤ F f (fun _ => 1 - Phi ((t - b * y) / a)) := by
    intro y
    have h2 := UniversalSubmod.lemma_2_1 f hf0 hf (1 - Phi ((t - b * y) / a))
      (by linarith [phi_le_one ((t - b * y) / a)]) (by linarith [phi_nonneg ((t - b * y) / a)])
    have h3 := phi_sq_bound ((t - b * y) / a)
    refine le_trans ?_ h2
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hO
    nlinarith
  have hint1 : Integrable (fun y : ℝ => OPT f * (1 / 4 - ((t - b * y) / a) ^ 2 / (2 * Real.pi)))
      (gaussianReal 0 1) := by
    refine Integrable.const_mul (Integrable.sub (integrable_const _) (Integrable.div_const ?_ _)) _
    have hm : MemLp (fun y : ℝ => (t - b * y) / a) 2 (gaussianReal 0 1) := by
      have h0 : MemLp (fun y : ℝ => t - b * y) 2 (gaussianReal 0 1) :=
        MemLp.sub (memLp_const t) (MemLp.const_mul (memLp_id_gaussianReal' (μ := 0) (v := 1) 2
          (by simp)) b)
      have h1 := h0.const_mul a⁻¹
      convert h1 using 2
      simp [div_eq_inv_mul]
    simpa using hm.integrable_sq
  have hq : Measurable (fun y : ℝ => 1 - Phi ((t - b * y) / a)) :=
    measurable_const.sub (phi_meas.comp (by fun_prop))
  have hint2 : Integrable (fun y : ℝ => F f (fun _ => 1 - Phi ((t - b * y) / a)))
      (gaussianReal 0 1) :=
    integrable_bdd _ (F_meas f _ hq) (∑ T, |f T|) (fun y =>
      F_bdd f _ (by linarith [phi_le_one ((t - b * y) / a)])
        (by linarith [phi_nonneg ((t - b * y) / a)]))
  calc OPT f * (1 / 4 - (t ^ 2 + b ^ 2) / (a ^ 2 * (2 * Real.pi)))
      = ∫ y : ℝ, OPT f * (1 / 4 - ((t - b * y) / a) ^ 2 / (2 * Real.pi)) ∂(gaussianReal 0 1) := by
        rw [integral_const_mul, gauss_quad a b t ha]
    _ ≤ _ := integral_mono hint1 hint2 h1


lemma semidefExt_gram {n k : ℕ} (f : Finset (Fin n) → ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (t : ℝ) :
    semidefExt f (fun _ => 1 - Phi t) (Matrix.gram ℝ v)
      = ∫ z, f (threshSet v z t) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
  unfold semidefExt
  rw [← law_gram v]
  have hg : Measurable (fun z : EuclideanSpace ℝ (Fin k) =>
      (WithLp.toLp 2 (fun i => ⟪v i, z⟫) : EuclideanSpace ℝ (Fin n))) := by fun_prop
  have hm : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      f (Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i)))) := by
    refine meas_comp (fun g : EuclideanSpace ℝ (Fin n) =>
      Finset.univ.filter (fun i => 1 - (1 - Phi t) ≤ Phi (g i))) (fun i => ?_) f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_const (phi_meas.comp (by fun_prop))
  rw [integral_map hg.aemeasurable hm.aestronglyMeasurable]
  congr 1
  funext z
  congr 1
  ext i
  simp [threshSet, phi_le_iff]

end UniversalSubmod.Dev.Thm24

namespace UniversalSubmod

open MeasureTheory ProbabilityTheory NonmonotoneSubmod.Shared
open scoped RealInnerProductSpace

theorem chk_theorem_2_4 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (v : Fin n → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ = 1)
    (hvv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ε)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin k)) (hZ : Measurable Z)
    (hZlaw : P.map Z = stdGaussian (EuclideanSpace ℝ (Fin k)))
    (T : Ω → ℝ) (hT : Measurable T) (hind : IndepFun Z T P) (hT2 : MemLp T 2 P)
    (hT0 : ∫ ω, T ω ∂P = 0) (hTvar : variance T P ≤ ε)
    (f : Finset (Fin n) → ℝ) (hf0 : ∀ S, 0 ≤ f S) (hf : Submodular f) :
    (1 / 4 - ε) * OPT f ≤ ∫ ω, f (threshSet v (Z ω) (T ω)) ∂P := by
  classical
  have hε : 0 < 1 - ε := by linarith
  have ha : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.2 hε
  have ha2 : Real.sqrt (1 - ε) ^ 2 = 1 - ε := Real.sq_sqrt hε.le
  have hb2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε0.le
  have hS' : CorrMatrix (Dev.Thm24.Sc (n := n) (Real.sqrt (1 - ε)) (Real.sqrt ε)) :=
    ⟨Dev.Thm24.Sc_psd _ _, fun i => by simp [Dev.Thm24.Sc, ha2, hb2]⟩
  have hS : CorrMatrix (Matrix.gram ℝ v) :=
    ⟨Matrix.posSemidef_gram ℝ v, fun i => by
      simp [Matrix.gram, real_inner_self_eq_norm_sq, hv i]⟩
  have hle : ∀ i j, i ≠ j →
      Matrix.gram ℝ v i j ≤ Dev.Thm24.Sc (Real.sqrt (1 - ε)) (Real.sqrt ε) i j := by
    intro i j hij
    simp only [Matrix.gram, Dev.Thm24.Sc, Matrix.of_apply, hij, if_false, zero_add, hb2]
    exact hvv i j hij
  have hpt : ∀ t : ℝ, OPT f * (1 / 4 - (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi)))
      ≤ ∫ z, f (threshSet v z t) ∂(stdGaussian (EuclideanSpace ℝ (Fin k))) := by
    intro t
    have hx : ∀ i : Fin n, (fun _ : Fin n => 1 - Cohen2019.Robust.Phi t) i ∈ Set.Icc (0 : ℝ) 1 :=
      fun i => ⟨by linarith [Dev.Thm24.phi_le_one t], by linarith [Dev.Thm24.phi_nonneg t]⟩
    have h23 := theorem_2_3 f hf0 hf _ _ hS hS' hle _ hx
    have h1 := Dev.Thm24.pointwise f hf0 hf (Real.sqrt (1 - ε)) (Real.sqrt ε) t ha
    rw [Dev.Thm24.semidefExt_gram] at h23
    rw [ha2, hb2] at h1
    exact h1.trans h23
  have hH : Measurable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2)) := by
    refine Dev.Thm24.meas_comp (fun p : EuclideanSpace ℝ (Fin k) × ℝ => threshSet v p.1 p.2) (fun i => ?_) f
    simp only [threshSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact measurableSet_le measurable_snd (by fun_prop)
  have hmap : P.map (fun ω => (Z ω, T ω))
      = (stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T) := by
    rw [← hZlaw]; exact hind.map_prod_eq_prod_map_map hZ.aemeasurable hT.aemeasurable
  haveI : IsProbabilityMeasure (P.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hI : ∫ ω, f (threshSet v (Z ω) (T ω)) ∂P
      = ∫ p, f (threshSet v p.1 p.2)
          ∂((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T)) := by
    rw [← hmap, integral_map (hZ.prodMk hT).aemeasurable hH.aestronglyMeasurable]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin k) × ℝ => f (threshSet v p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin k))).prod (P.map T)) :=
    Dev.Thm24.integrable_bdd _ hH _ (fun p => Dev.Thm24.f_bdd f _)
  rw [hI, integral_prod_symm _ hint]
  have hint_t2 : Integrable (fun t : ℝ => t ^ 2) (P.map T) := by
    rw [integrable_map_measure (by fun_prop) hT.aemeasurable]
    exact hT2.integrable_sq
  have hET : ∫ t : ℝ, t ^ 2 ∂(P.map T) = variance T P := by
    rw [integral_map hT.aemeasurable (by fun_prop), variance_eq_sub hT2]
    simp [hT0]
  have hD : 0 < (1 - ε) * (2 * Real.pi) := by positivity
  have hcint : Integrable (fun t : ℝ => OPT f * (1 / 4 - (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi))))
      (P.map T) :=
    ((integrable_const _).sub ((hint_t2.add (integrable_const ε)).div_const _)).const_mul _
  have hcval : ∫ t : ℝ, OPT f * (1 / 4 - (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi))) ∂(P.map T)
      = OPT f * (1 / 4 - (variance T P + ε) / ((1 - ε) * (2 * Real.pi))) := by
    have hi3 : Integrable (fun t : ℝ => (t ^ 2 + ε) / ((1 - ε) * (2 * Real.pi))) (P.map T) :=
      (hint_t2.add (integrable_const ε)).div_const _
    rw [integral_const_mul, integral_sub (integrable_const _) hi3,
      integral_div _ (fun t : ℝ => t ^ 2 + ε)]
    have hi4 : ∫ t : ℝ, (t ^ 2 + ε) ∂(P.map T) = variance T P + ε := by
      rw [integral_add hint_t2 (integrable_const ε), hET]; simp
    rw [hi4]
    simp
  calc (1 / 4 - ε) * OPT f
      ≤ OPT f * (1 / 4 - (variance T P + ε) / ((1 - ε) * (2 * Real.pi))) := by
        have hO := Dev.Thm24.OPT_nonneg f hf0
        have hπ := Real.pi_gt_three
        have : (variance T P + ε) / ((1 - ε) * (2 * Real.pi)) ≤ ε := by
          rw [div_le_iff₀ hD]
          have h2 : 2 ≤ (1 - ε) * (2 * Real.pi) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h2 hε0.le]
        nlinarith [mul_le_mul_of_nonneg_left this hO]
    _ = _ := hcval.symm
    _ ≤ _ := integral_mono hcint hint.integral_prod_right hpt

end UniversalSubmod
end

theorem solution : type_of% @UniversalSubmod.chk_theorem_2_4 := @UniversalSubmod.chk_theorem_2_4
