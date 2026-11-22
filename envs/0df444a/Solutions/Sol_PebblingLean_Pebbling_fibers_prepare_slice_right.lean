-- Prove2me | solution 1 for PebblingLean.Pebbling.fibers_prepare_slice_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:37.171864+00:00
-- url     : https://prove2.me/submissions/2580c8b8-386e-410d-b06d-39c40b8e8b5b

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_fibers_reaches_of_forall_reaches
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [Finite W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {F : W → Pebbling V} {x : V}
    (hcan : ∀ z : W, CanReachAtLeast G (F z) x (E z)) :
    ∃ Dprep : Pebbling (V × W),
      Reaches (Graph.cartesianProduct G H) (fibersDistribution F) Dprep ∧
        Dominates Dprep (sliceDistribution x E) := by
  classical
  choose F' hreach htarget using hcan
  refine ⟨fibersDistribution F', ?_, ?_⟩
  · exact fibers_reaches_of_forall_reaches (G := G) (H := H) hreach
  · intro p
    cases p with
    | mk v z =>
      by_cases hv : v = x
      · simp_all
      · simp [fibersDistribution, sliceDistribution, hv]
end PebblingLean.Pebbling
