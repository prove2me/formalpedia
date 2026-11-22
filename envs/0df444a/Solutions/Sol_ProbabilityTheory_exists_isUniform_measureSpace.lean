-- Prove2me | solution 1 for ProbabilityTheory.exists_isUniform_measureSpace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:39.719641+00:00
-- url     : https://prove2.me/submissions/0ddc9a9d-66b6-4f66-908b-c16b13b74b24

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_exists_isUniform

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
    [MeasurableSingletonClass S] (H : Finset S) (h : H.Nonempty) :
    ∃ (Ω : Type uS) (mΩ : MeasureSpace Ω) (U : Ω → S),
    IsProbabilityMeasure (ℙ : Measure Ω) ∧ Measurable U ∧ IsUniform H U ∧ (∀ ω : Ω,
      U ω ∈ H) ∧
      FiniteRange U := by
  rcases exists_isUniform H h with ⟨Ω, mΩ, X, μ, hμ, Xmeas, Xunif, Xmem, Xfin⟩
  exact ⟨Ω, ⟨μ⟩, X, hμ, Xmeas, Xunif, Xmem, Xfin⟩
end ProbabilityTheory
