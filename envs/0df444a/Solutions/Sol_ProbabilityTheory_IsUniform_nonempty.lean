-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:05.500955+00:00
-- url     : https://prove2.me/submissions/0e34fc70-bfac-4454-9c29-811e3c8475bc

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
theorem _root_.solution
    {H : Finset S} (h : IsUniform H X μ) [hμ : NeZero μ] : H.Nonempty := by
  rcases Finset.eq_empty_or_nonempty H with rfl|h'
  · simpa [hμ.out] using h.measure_preimage_compl
  · exact h'
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
