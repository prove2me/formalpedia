-- Prove2me | solution 1 for ProbabilityTheory.condMutualInfo_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:09:59.759829+00:00
-- url     : https://prove2.me/submissions/813aa1f6-e489-4d07-9575-e31e5281cef4

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_P2M_ProbabilityTheory_condEntropy_of_injective__9847cc7a9a3e
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk


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
theorem _root_.solution [Countable U]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    {f : U → V} (hf : Function.Injective f) :
    I[X : Y | f ∘ Z; μ] = I[X : Y | Z; μ] := by
  have hfZ : Measurable (f ∘ Z) := by fun_prop
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX hY hfZ,
    condEntropy_of_injective' _ hX hZ _ hf hfZ, condEntropy_of_injective' _ hY hZ _ hf hfZ,
    condEntropy_of_injective' _ (hX.prodMk hY) hZ _ hf hfZ]
end _root_.ProbabilityTheory
end ProbabilityTheory
