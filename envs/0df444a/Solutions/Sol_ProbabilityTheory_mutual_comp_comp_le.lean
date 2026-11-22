-- Prove2me | solution 1 for ProbabilityTheory.mutual_comp_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:10:08.881901+00:00
-- url     : https://prove2.me/submissions/0c118f9a-e86a-459c-8a01-7c868b4a2be7

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_mutualInfo_comm
public import Theorems.Thm_ProbabilityTheory_mutual_comp_le
public import Theorems.Thm_ProbabilityTheory_IsUniform_comp


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
universe uΩ uS uT uU uV uW
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU} {V : Type uV} {W : Type uW}
  [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSpace V] [MeasurableSpace W]
  [Countable S] [Countable T] [Countable V] [Countable W]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [MeasurableSingletonClass V] [MeasurableSingletonClass W]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
  {μ : Measure Ω}
namespace ProbabilityTheory
theorem _root_.solution [Countable U] (μ : Measure Ω) [IsProbabilityMeasure μ] (hX :
  Measurable X)
    (hY : Measurable Y) (f : S → U) (g : T → V) (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[f ∘ X : g ∘ Y; μ] ≤ I[X : Y; μ] :=
  calc
    _ ≤ I[X : g ∘ Y; μ] := mutual_comp_le μ hX (Measurable.comp hg hY) f
    _ = I[g ∘ Y : X; μ] := mutualInfo_comm hX (Measurable.comp hg hY) μ
    _ ≤ I[Y : X; μ] := mutual_comp_le μ hY hX g
    _ = I[X : Y; μ] := mutualInfo_comm hY hX μ
end ProbabilityTheory
