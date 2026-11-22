-- Prove2me | solution 1 for PebblingLean.Pebbling.slice_move_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:48.141306+00:00
-- url     : https://prove2.me/submissions/9c1e83b9-1ed9-43fe-9d79-0344a8f3b07c

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
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
theorem _root_.solution [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hmove : Move H E F) :
    Move (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(x, u), (x, v), ?_, ?_, ?_⟩
  · exact Or.inr ⟨rfl, huv⟩
  · simpa [sliceDistribution] using hE
  · funext p
    by_cases hpx : p.1 = x
    · cases p with
      | mk x' z =>
        simp only at hpx
        subst x'
        by_cases hzu : z = u
        · simp_all
        · by_cases hzv : z = v
          · simp_all
          · simp [sliceDistribution, moveDistribution, hzu, hzv]
    · cases p with
      | mk x' z =>
        simp_all
end PebblingLean.Pebbling
