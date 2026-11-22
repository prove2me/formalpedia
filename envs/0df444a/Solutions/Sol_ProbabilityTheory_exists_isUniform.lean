-- Prove2me | solution 1 for ProbabilityTheory.exists_isUniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:52.594953+00:00
-- url     : https://prove2.me/submissions/45b2c2e8-16f2-4673-88cf-277ff91d0195

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
namespace ProbabilityTheory
theorem _root_.solution [MeasurableSpace S] [MeasurableSingletonClass S]
    (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (_ : MeasurableSpace Ω) (X : Ω → S) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧ Measurable X ∧ IsUniform H X μ ∧ (∀ ω,
        X ω ∈ H) ∧ FiniteRange X := by
  refine ⟨H, Subtype.instMeasurableSpace, fun x ↦ x,
    (Finset.card H : ℝ≥0∞)⁻¹ • ∑ i, .dirac i, ?_,
    measurable_subtype_coe, ⟨?_, ?_⟩, fun x ↦ x.2, ?_⟩
  · constructor
    simp only [Finset.univ_eq_attach, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
      measure_univ, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one, smul_eq_mul]
    rw [ENNReal.inv_mul_cancel]
    · simpa using h.ne_empty
    · simp
  · intro x hx y hy
    simp only [Finset.univ_eq_attach, Measure.smul_apply, Measure.coe_finsetSum,
      Finset.sum_apply, Measure.dirac_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ⟨x, hx⟩, Finset.sum_eq_single ⟨y, hy⟩]
    · simp
    · simp_all
    · simp
    · simp_all
    · simp
  · simp
  · apply finiteRange_of_finset _ H _
    simp
end ProbabilityTheory
