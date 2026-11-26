-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_image_eq_of_kernel_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:48.701168+00:00
-- url     : https://prove2.me/submissions/44cbd54a-ee83-44f7-a796-259064ae968a

module
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimension
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Linarith
public import Definitions.Def_SumOfSetsInSeveralDimensions_AffineDimSumset
public import Definitions.Def_SumOfSetsInSeveralDimensions_LowerBound
public import Definitions.Def_SumOfSetsInSeveralDimensions_FreimanDimensionSumsetBounds

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    {s : Finset α} {f : α → β} {g : α → γ}
    (h : ∀ x ∈ s, ∀ y ∈ s, (f x = f y ↔ g x = g y)) :
    #(s.image f) = #(s.image g) := by
  apply card_bij (fun b hb ↦ g (mem_image.mp hb).choose)
  · intro b hb
    exact mem_image_of_mem g (mem_image.mp hb).choose_spec.1
  · intro b₁ hb₁ b₂ hb₂ hgb
    obtain ⟨hx₁, hfb₁⟩ := (mem_image.mp hb₁).choose_spec
    obtain ⟨hx₂, hfb₂⟩ := (mem_image.mp hb₂).choose_spec
    exact hfb₁ ▸ hfb₂ ▸ (h _ hx₁ _ hx₂).2 hgb
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
    obtain ⟨hy, hfy⟩ := (mem_image.mp (mem_image_of_mem f hx)).choose_spec
    exact ⟨f x, mem_image_of_mem f hx, (h _ hy _ hx).1 hfy⟩
end SumOfSetsInSeveralDimensions
