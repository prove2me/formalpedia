-- Prove2me | solution 1 for ProbabilityTheory.iIndepFun.inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:02.485591+00:00
-- url     : https://prove2.me/submissions/5d0819c1-ac16-4c90-8d85-16f79136e573

module
public import Mathlib.Probability.Independence.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Kernel_IndepFun
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory MeasurableSpace Measure Set
open scoped MeasureTheory ENNReal
open ProbabilityTheory
variable {Ω ι β γ : Type*} {κ : ι → Type*}
variable {β β' γ γ' : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω
  → β} {g : Ω → β'}
variable {Ω ι ι' : Type*} [MeasurableSpace Ω] {α β : ι → Type*}
  [n : ∀ i, MeasurableSpace (α i)]
  [m : ∀ i, MeasurableSpace (β i)] {f : ∀ i, Ω → α i}
  {μ : Measure Ω}
variable (i : ι) [Inv (α i)] [MeasurableInv (α i)] [DecidableEq ι]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.iIndepFun
theorem _root_.solution
    (h : iIndepFun f μ) : iIndepFun (update f i (f i)⁻¹) μ := by
  convert h.comp (update (fun _ ↦ id) i (·⁻¹)) _ with j
  · by_cases hj : j = i
    · subst hj; ext x; simp
    · simp [hj]
  intro j
  by_cases hj : j = i
  · subst hj; simp [measurable_inv]
  · simp [hj, measurable_id]
end _root_.ProbabilityTheory.iIndepFun
end ProbabilityTheory
