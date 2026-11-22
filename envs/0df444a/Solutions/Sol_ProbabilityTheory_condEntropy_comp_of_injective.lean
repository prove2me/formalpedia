-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_comp_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:57:50.764201+00:00
-- url     : https://prove2.me/submissions/69e2f35d-e3f4-48b4-ad17-f849027ca23e

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable {X : Ω → S} {Y : Ω → T}
variable [MeasurableSingletonClass T]
variable [MeasurableSingletonClass S]
variable [Countable S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution {Y : Ω → U}
    (μ : Measure Ω) (hX : Measurable X) (f : S → T) (hf : Injective f) :
    H[f ∘ X | Y; μ] = H[X | Y; μ] :=
  integral_congr_ae (ae_of_all _ (fun _ ↦ entropy_comp_of_injective _ hX f hf))
end _root_.ProbabilityTheory
end ProbabilityTheory
