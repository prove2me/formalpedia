-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:36.977883+00:00
-- url     : https://prove2.me/submissions/8e1e6b40-a835-41e8-a872-6425716d2e46

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
    [DecidableEq T] {H : Finset S} (h : IsUniform H X μ) {f : S → T}
    (hf : Injective f) : IsUniform (Finset.image f H) (f ∘ X) μ where
  eq_of_mem := by
    intro x hx y hy
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    have A z : f ⁻¹' {f z} = {z} := by ext; simp [hf.eq_iff]
    simp [preimage_comp, A, h.eq_of_mem hx hy]
  measure_preimage_compl := by simpa [preimage_comp, hf] using h.measure_preimage_compl
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory
