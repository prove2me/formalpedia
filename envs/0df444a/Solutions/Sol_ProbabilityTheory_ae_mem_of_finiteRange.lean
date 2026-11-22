-- Prove2me | solution 1 for ProbabilityTheory.ae_mem_of_finiteRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:14.378571+00:00
-- url     : https://prove2.me/submissions/d2c42c22-4b2d-4e56-9d28-0c97a3b65d19

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
public import Theorems.Thm_ProbabilityTheory_full_measure_of_finiteRange

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
theorem _root_.solution {μ : Measure Ω} {X : Ω
  → S} (hX : Measurable X) [hX' : FiniteRange X] :
    ∀ᵐ x ∂μ.map X, x ∈ hX'.toFinset := full_measure_of_finiteRange hX
end ProbabilityTheory
