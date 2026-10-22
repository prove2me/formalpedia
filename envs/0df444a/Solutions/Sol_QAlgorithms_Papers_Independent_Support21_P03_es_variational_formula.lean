-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P03.es_variational_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:54:37.573692+00:00
-- url     : https://prove2.me/submissions/2133653d-4f6b-4e05-8f2d-c9811795d4d0

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P03
noncomputable section

open MeasureTheory Filter Set

open scoped ENNReal Topology BigOperators

open QAlgorithms.Papers.Independent.Support21.P03

lemma g68f_ext {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (ℓ : X → ℝ)
    (h : Integrable ℓ ν) :
    QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation ν ℓ = ((∫ x, ℓ x ∂ν : ℝ) : EReal) := by
  have hneg : ∫⁻ x, ENNReal.ofReal (-ℓ x) ∂ν ≠ ∞ := h.neg.lintegral_lt_top.ne
  unfold QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h,
    ← EReal.coe_ennreal_toReal h.lintegral_lt_top.ne, ← EReal.coe_ennreal_toReal hneg,
    ← EReal.coe_sub]

lemma g68f_gibbs {X : Type*} [MeasurableSpace X] (ω : Measure X) [IsProbabilityMeasure ω]
    (ℓ : X → ℝ) (hm : Measurable ℓ) (C : ℝ) (hC : ∀ᵐ x ∂ω, |ℓ x| ≤ C) (α : ℝ) :
    ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (α * ℓ x)) ∂ω) =
      sSup {v : EReal | ∃ nu : ProbabilityMeasure X, (nu : Measure X) ≪ ω ∧
        v = signedEntropy (nu : Measure X) ω +
          (α : EReal) * QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (nu : Measure X) ℓ} := by
  set f : X → ℝ := fun x => α * ℓ x with hfdef
  have hfm : Measurable f := hm.const_mul α
  have hexp : Integrable (fun x => Real.exp (f x)) ω := by
    refine Integrable.mono' (integrable_const (Real.exp (|α| * C))) (by fun_prop) ?_
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc f x ≤ |α * ℓ x| := le_abs_self _
      _ = |α| * |ℓ x| := abs_mul _ _
      _ ≤ |α| * C := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hℓ : ∀ ν : Measure X, IsFiniteMeasure ν → ν ≪ ω → Integrable ℓ ν := by
    intro ν _ hac
    refine Integrable.mono' (integrable_const C) hm.aestronglyMeasurable ?_
    filter_upwards [hac.ae_le hC] with x hx
    rwa [Real.norm_eq_abs]
  set Z := ∫ x, Real.exp (f x) ∂ω
  have hZ : 0 < Z := integral_exp_pos hexp
  have hlhs : ENNReal.log (∫⁻ x, ENNReal.ofReal (Real.exp (α * ℓ x)) ∂ω) = (Real.log Z : EReal) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hexp (ae_of_all _ fun x => (Real.exp_pos _).le),
      ENNReal.log_ofReal_of_pos hZ]
  rw [hlhs]
  set νs := ω.tilted f
  haveI hνs : IsProbabilityMeasure νs := isProbabilityMeasure_tilted hexp
  refine Eq.symm (IsGreatest.csSup_eq ⟨⟨(⟨νs, hνs⟩ : ProbabilityMeasure X), tilted_absolutelyContinuous ω f, ?_⟩, ?_⟩)
  · -- attainment
    have hacs : νs ≪ ω := tilted_absolutelyContinuous ω f
    have hllr : llr νs ω =ᵐ[νs] fun x => f x - Real.log Z := by
      have h1 := llr_tilted_left (μ := ω) (ν := ω) (Measure.AbsolutelyContinuous.refl ω) hexp hfm.aemeasurable
      filter_upwards [hacs.ae_le h1, hacs.ae_le (llr_self ω)] with x hx hx'
      rw [hx, hx']; simp [Z]
    have hfi : Integrable f νs := (hℓ νs inferInstance hacs).const_mul α
    have hint : Integrable (llr νs ω) νs := (hfi.sub (integrable_const _)).congr hllr.symm
    have hval : ∫ x, llr νs ω x ∂νs = ∫ x, f x ∂νs - Real.log Z := by
      rw [integral_congr_ae hllr, integral_sub hfi (integrable_const _)]; simp
    have hnn : 0 ≤ ∫ x, llr νs ω x ∂νs := by
      have := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hacs hint
      simpa using this
    show (Real.log Z : EReal) = signedEntropy νs ω + (α : EReal) *
      QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation νs ℓ
    rw [g68f_ext νs ℓ (hℓ νs inferInstance hacs), signedEntropy,
      InformationTheory.klDiv_of_ac_of_integrable hacs hint]
    simp only [probReal_univ, add_sub_cancel_right]
    rw [EReal.coe_ennreal_ofReal, max_eq_left hnn, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_add,
      EReal.coe_eq_coe_iff, hval]
    simp only [hfdef, integral_const_mul]
    ring
  · -- upper bound
    rintro v ⟨ν, hac, rfl⟩
    have hℓν := hℓ ν inferInstance hac
    rw [g68f_ext (ν : Measure X) ℓ hℓν, signedEntropy]
    by_cases hint : Integrable (llr (ν : Measure X) ω) ν
    · rw [InformationTheory.klDiv_of_ac_of_integrable hac hint]
      simp only [probReal_univ, add_sub_cancel_right]
      have hnn : 0 ≤ ∫ x, llr (ν : Measure X) ω x ∂(ν : Measure X) := by
        have := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hint
        simpa using this
      rw [EReal.coe_ennreal_ofReal, max_eq_left hnn, ← EReal.coe_neg, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_le_coe_iff]
      have hfi : Integrable f ν := hℓν.const_mul α
      have hac' : (ν : Measure X) ≪ νs := hac.trans (absolutelyContinuous_tilted hexp)
      have hrt := llr_tilted_right (μ := (ν : Measure X)) (ν := ω) hac hexp
      have hint' : Integrable (llr (ν : Measure X) νs) ν :=
        ((hfi.neg.add (integrable_const _)).add hint).congr hrt.symm
      have hG := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac' hint'
      simp only [probReal_univ, add_sub_cancel_right] at hG
      rw [integral_llr_tilted_right hac hfi hexp hint] at hG
      have : ∫ x, f x ∂(ν : Measure X) = α * ∫ x, ℓ x ∂(ν : Measure X) := integral_const_mul _ _
      linarith
    · rw [InformationTheory.klDiv_of_not_integrable hint]
      simp

variable {K : TimeKind} {M : Type*} [MeasurableSpace M]

lemma g68f_meas_ell (D : NonsingularSystem K M) (t : K.Carrier) : Measurable (logDensity D t) :=
  Real.measurable_log.comp (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv _ _))

/-- Equation (3.11), PDF p.10: the supremum ranges over normal probability
measures, and log RN density must be essentially bounded. -/
theorem solution (D : NonsingularSystem K M) (t : K.Carrier)
    (hbounded : MemLp (logDensity D t) ∞ (D.omega : Measure M))
    (alpha : ℝ) :
    finiteES D t alpha = sSup {v : EReal | ∃ nu : ProbabilityMeasure M,
      (nu : Measure M) ≪ (D.omega : Measure M) ∧
      v = signedEntropy (nu : Measure M) (D.omega : Measure M) +
        (alpha : EReal) * QAlgorithms.Papers.Independent.Next46.P01.extendedExpectation (nu : Measure M) (logDensity D t)} := by
  have hE : eLpNormEssSup (logDensity D t) (D.omega : Measure M) ≠ ⊤ := by
    have := hbounded.2
    rw [eLpNorm_exponent_top] at this
    exact this.ne
  refine g68f_gibbs _ _ (g68f_meas_ell D t) (eLpNormEssSup (logDensity D t) (D.omega : Measure M)).toReal ?_ alpha
  filter_upwards [ae_le_eLpNormEssSup (f := logDensity D t) (μ := (D.omega : Measure M))] with x hx
  rw [Real.enorm_eq_ofReal_abs] at hx
  exact (ENNReal.ofReal_le_iff_le_toReal hE).mp hx
