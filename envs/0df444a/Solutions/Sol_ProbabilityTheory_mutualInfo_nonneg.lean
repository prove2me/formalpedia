-- Prove2me | solution 1 for ProbabilityTheory.mutualInfo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:52.502551+00:00
-- url     : https://prove2.me/submissions/830c2bef-83ff-4279-a335-cee23f85b177

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_def


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω)
    [FiniteRange X] [FiniteRange Y] :
    0 ≤ I[X : Y; μ] := by
  simp_rw [mutualInfo_def, entropy_def]
  have h_fst : μ.map X = (μ.map (⟨X, Y⟩)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (hX.prodMk hY)]
    congr
  have h_snd : μ.map Y = (μ.map (⟨X, Y⟩)).map Prod.snd := by
    rw [Measure.map_map measurable_snd (hX.prodMk hY)]
    congr
  rw [h_fst, h_snd]
  exact measureMutualInfo_nonneg
end _root_.ProbabilityTheory
end ProbabilityTheory
