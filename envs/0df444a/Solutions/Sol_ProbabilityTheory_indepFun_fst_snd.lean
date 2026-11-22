-- Prove2me | solution 1 for ProbabilityTheory.indepFun_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:25:29.848806+00:00
-- url     : https://prove2.me/submissions/154bd356-2779-4fe7-bf1c-8eb7f7146993

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Theorems.Thm_ProbabilityTheory_iIndepFun_inv
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
attribute [local simp] ProbabilityTheory.indepFun_zero_measure

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω' α : Type*} [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [IsZeroOrProbabilityMeasure μ] {μ'} [IsZeroOrProbabilityMeasure μ'] :
    IndepFun (Prod.fst : Ω × Ω' → Ω) (Prod.snd : Ω × Ω' → Ω') (μ.prod μ') := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ' with rfl | hμ'
  · simp
  rw [IndepFun_iff]
  rintro _ _ ⟨s, _, rfl⟩ ⟨t, _, rfl⟩
  simp [← Set.prod_univ, ← Set.univ_prod, Set.prod_inter_prod]
end _root_.ProbabilityTheory
end ProbabilityTheory
