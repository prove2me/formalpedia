-- Prove2me | solution 1 for ProbabilityTheory.measureEntropy_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:59.803799+00:00
-- url     : https://prove2.me/submissions/65829894-81eb-4cad-b6b0-fb17a7848f83

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
    (μ : Measure T) (f : T → S) (hf_m : Measurable f) (hf : Function.Injective f) :
    Hm[μ.map f] = Hm[μ] := by
  have : μ.map f Set.univ = μ Set.univ := by
      simp_all
  simp_rw [measureEntropy, Measure.ennreal_smul_real_apply,
    map_measureReal_apply hf_m (.singleton _)]
  rw [this]
  classical
  let F (x : S) : ℝ := negMulLog ((μ Set.univ)⁻¹.toReal • μ.real (f ⁻¹' {x}))
  have : ∑' x : S, F x
      = ∑' x : (f '' Set.univ), F x := by
    apply (tsum_subtype_eq_of_support_subset _).symm
    intro x hx
    contrapose hx
    suffices f ⁻¹' {x} = ∅ by simp [F, this]
    contrapose! hx
    rw [Set.image_univ]
    exact hx
  rw [this, tsum_image _ hf.injOn, tsum_univ fun x ↦ F (f x)]
  congr! with s
  ext s'
  simpa using hf.eq_iff
end _root_.ProbabilityTheory
end ProbabilityTheory
