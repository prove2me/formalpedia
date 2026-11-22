-- Prove2me | solution 1 for ProbabilityTheory.measureEntropy_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:23.931375+00:00
-- url     : https://prove2.me/submissions/83df7469-8662-479d-b2dd-0fd08633bdd2

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
public import Theorems.Thm_MeasureTheory_Measure_comap_real_apply
public import Theorems.Thm_MeasureTheory_Measure_ennreal_smul_real_apply
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
namespace _root_.ProbabilityTheory
theorem _root_.solution
    (μ : Measure T) (f : S → T) (hf : MeasurableEmbedding f)
    (hf_range : Set.range f =ᵐ[μ] Set.univ) :
    Hm[μ.comap f] = Hm[μ] := by
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _),
    Measure.comap_apply f hf.injective hf.measurableSet_image' _ MeasurableSet.univ]
  simp only [Set.image_univ, Set.image_singleton, smul_eq_mul]
  classical
  rw [← tsum_range (f :=
    fun x ↦ negMulLog ((μ (Set.range f))⁻¹.toReal * μ.real {x})) (g := f)
    hf.injective, measure_congr hf_range ]
  let F (x : T) : ℝ := negMulLog ((μ .univ)⁻¹.toReal * μ.real {x})
  change ∑' x : (Set.range f), F x = ∑' x : T, F x
  apply tsum_subtype_eq_of_support_subset
  intro x hx
  contrapose hx
  suffices μ {x} = 0 by simp [F, Measure.real, this]
  simp only [ae_eq_univ] at hf_range
  exact measure_mono_null (by simp [*]) hf_range
end _root_.ProbabilityTheory
end ProbabilityTheory
