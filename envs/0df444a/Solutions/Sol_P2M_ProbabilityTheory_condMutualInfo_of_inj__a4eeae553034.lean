-- Prove2me | solution 1 for P2M_ProbabilityTheory_condMutualInfo_of_inj__a4eeae553034
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:15:00.95873+00:00
-- url     : https://prove2.me/submissions/27a6eb92-0678-4261-b1c1-86aa81aa2a4b

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_comm
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_of_inj_map
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_of_inj

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
variable [Countable S] [Countable T]
variable [MeasurableSingletonClass U]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    {S T U S' T' U' Ω : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Countable T]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    [MeasurableSpace S'] [MeasurableSingletonClass S'] [Countable S']
    [MeasurableSpace T'] [MeasurableSingletonClass T'] [Countable T']
    [MeasurableSpace U'] [MeasurableSingletonClass U'] [Countable U']
    {X : Ω → S} {Y : Ω → T} {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {f : S → S'} (hf : Function.Injective f)
    {g : T → T'} (hg : Function.Injective g)
    {h : U → U'} (hh : Function.Injective h)
    : I[f ∘ X : g ∘ Y | h ∘ Z; μ] = I[X : Y | Z; μ] := calc
    _ = I[f ∘ X : g ∘ Y | Z; μ] := by rw [condMutualInfo_of_inj _ _ _ _ hh] <;> try fun_prop
    _ = I[X : g ∘ Y | Z; μ] := by
      convert condMutualInfo_of_inj_map hX _ hZ (fun _ ↦ f) (fun _ ↦ hf) <;> try infer_instance
      all_goals first | rfl | fun_prop
    _ = I[g ∘ Y : X | Z; μ] := by apply condMutualInfo_comm <;> fun_prop
    _ = I[Y : X | Z; μ] := by
      convert condMutualInfo_of_inj_map hY _ hZ (fun _ ↦ g) (fun _ ↦ hg) <;> try infer_instance
      all_goals first | rfl | fun_prop
    _ = _ := by apply condMutualInfo_comm <;> fun_prop
end _root_.ProbabilityTheory
end ProbabilityTheory
