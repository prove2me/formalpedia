-- Prove2me | solution 1 for P2M_ProbabilityTheory_exists_isUniform_measureSpace__68d4ee0dc9af
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:49.345632+00:00
-- url     : https://prove2.me/submissions/f7f9611f-53c1-4f33-9434-3a3bd8872b7f

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_exists_isUniform_measureSpace

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
theorem _root_.solution {S : Type uS} [MeasurableSpace S]
    [MeasurableSingletonClass S] (H : Set S) (hH : H.Finite) (h'H : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U
      ∧ (∀ ω, U ω ∈ H) ∧ FiniteRange U := by
  set Hf := hH.toFinset
  have hHf : Hf.Nonempty := by simpa [Hf] using h'H
  obtain ⟨Ω, mΩ, U, hμ, hmes, hunif, hrange, hfin⟩ := exists_isUniform_measureSpace Hf hHf
  simp only [Finite.coe_toFinset, Finite.mem_toFinset, Hf] at hunif hrange
  exact ⟨Ω, mΩ, U, hμ, hmes, hunif, hrange, hfin⟩
end ProbabilityTheory
