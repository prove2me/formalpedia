-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.isAddFreimanIso_rationalVectorToReal_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:21.946358+00:00
-- url     : https://prove2.me/submissions/74a4964e-fc9e-4d39-af0a-306330a1b50d

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_rationalVectorToReal_injective
public import Theorems.Thm_SumOfSetsInSeveralDimensions_rationalVectorToReal_add
public import Theorems.Thm_Finset_affineDim_empty
public import Theorems.Thm_Finset_affineDim_singleton
public import Theorems.Thm_Finset_affineDim_vadd_finset
attribute [local simp] Finset.affineDim_empty
attribute [local simp] Finset.affineDim_singleton
attribute [local simp] Finset.affineDim_vadd_finset



set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G : Type*} [AddCommMonoid G] {d : ℕ}
    {X : Finset G} {f : G → (Fin d → ℚ)}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set (Fin d → ℚ)) f) :
    IsAddFreimanIso 2 (X : Set G) (X.image (rationalVectorToReal ∘ f) : Set (Fin d → ℝ))
      (rationalVectorToReal ∘ f) := by
  rw [isAddFreimanIso_two] at hf ⊢
  constructor
  · rw [coe_image]
    exact (rationalVectorToReal_injective.comp_injOn hf.1.injOn).bijOn_image
  · intro a ha b hb c hc e he
    simp only [Function.comp, ← rationalVectorToReal_add, rationalVectorToReal_injective.eq_iff]
    exact hf.2 a ha b hb c hc e he
end SumOfSetsInSeveralDimensions
