-- Prove2me | solution 1 for SumOfSetsInSeveralDimensions.card_add_image_of_isAddFreimanIso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:17.148609+00:00
-- url     : https://prove2.me/submissions/f14eb120-f547-4030-ae0e-bda12ea7f43d

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
public import Theorems.Thm_SumOfSetsInSeveralDimensions_card_image_eq_of_kernel_iff

set_option autoImplicit true
@[expose] public section
public section
open SumOfSetsInSeveralDimensions
open Finset
open scoped Pointwise
noncomputable section
namespace SumOfSetsInSeveralDimensions
theorem _root_.solution {G H : Type*} [DecidableEq G] [DecidableEq H]
    [AddCommMonoid G] [AddCommMonoid H] {X A B : Finset G} {f : G → H}
    (hf : IsAddFreimanIso 2 (X : Set G) (X.image f : Set H) f) (hAX : A ⊆ X) (hBX : B ⊆ X) :
    #(A.image f + B.image f) = #(A + B) := by
  rw [add_def, add_def, ← prodMap_image_product, image_image]
  apply card_image_eq_of_kernel_iff
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab'
  obtain ⟨ha, hb⟩ := mem_product.1 hab
  obtain ⟨ha', hb'⟩ := mem_product.1 hab'
  exact hf.add_eq_add (hAX ha) (hBX hb) (hAX ha') (hBX hb')
end SumOfSetsInSeveralDimensions
