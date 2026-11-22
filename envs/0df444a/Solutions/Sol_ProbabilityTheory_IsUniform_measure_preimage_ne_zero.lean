-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.measure_preimage_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:14.663641+00:00
-- url     : https://prove2.me/submissions/313a0fc7-24c0-4171-9310-c1c3dc3c23da

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IsUniform
theorem _root_.solution
    {H : Finset S} [NeZero μ] (h : IsUniform H X μ)
    (hX : Measurable X) {H' : Set S} (h' : (H' ∩ H).Nonempty) : μ (X ⁻¹' H') ≠ 0 := by
  have : Nonempty (H' ∩ H : Set S) := h'.to_subtype
  simp only [h.measure_preimage hX H', ne_eq, ENNReal.div_eq_zero_iff, ENNReal.natCast_ne_top,
    or_false, NeZero.ne]
  exact not_false
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
