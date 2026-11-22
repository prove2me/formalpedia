-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.ae_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:02.823+00:00
-- url     : https://prove2.me/submissions/eb3f687a-04fd-40e2-b9de-8c9b23c5595a

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
namespace _root_.ProbabilityTheory.IsUniform
theorem _root_.solution (h : IsUniform H X μ) : ∀ᵐ ω ∂μ,
  X ω ∈ H := h.measure_preimage_compl
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
