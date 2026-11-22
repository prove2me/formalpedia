-- Prove2me | solution 1 for ProbabilityTheory.indepFun_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:27:53.080445+00:00
-- url     : https://prove2.me/submissions/5ccaf493-e902-441b-8c3c-6beb0625435c

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
    [IsZeroOrProbabilityMeasure μ] (c : α) : IndepFun f (fun _ => c) μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  rw [IndepFun_iff, MeasurableSpace.comap_const]
  intro t₁ t₂ _ ht₂
  rcases MeasurableSpace.measurableSet_bot_iff.mp ht₂ with h | h
  all_goals simp [h]
end _root_.ProbabilityTheory
end ProbabilityTheory
