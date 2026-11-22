-- Prove2me | solution 1 for ProbabilityTheory.integrable_of_finiteSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:22.804992+00:00
-- url     : https://prove2.me/submissions/b013d59d-8136-4ad4-8ac7-6d2243fb182e

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]
variable {μ : Measure S}
variable [MeasurableSingletonClass S]
namespace ProbabilityTheory
theorem _root_.solution (μ : Measure S) [FiniteSupport μ]
    {β : Type*} [NormedAddCommGroup β] [IsFiniteMeasure μ] [Countable S]
    {f : S → β} :
    Integrable f μ := by
  let A := μ.finiteSupport
  have hA : μ Aᶜ = 0 := measure_compl_support μ
  by_cases hA' : A = ∅
  · simp_all
  have : ∃ s₀, s₀ ∈ A := by
    contrapose! hA'
    ext s
    simpa using hA' s
  rcases this with ⟨s₀, hs₀⟩
  let f' : A → β := fun a ↦ f a
  classical
  let g : S → A := fun s ↦ if h : s ∈ A then ⟨s, h⟩ else ⟨s₀, hs₀⟩
  have : (f' ∘ g) =ᵐ[μ] f := by
    apply Filter.eventuallyEq_of_mem (s := A) hA
    intro a ha
    simp at ha
    simp [f', g, ha]
  apply Integrable.congr _ this
  apply Integrable.comp_measurable .of_finite
  fun_prop
end ProbabilityTheory
