-- Prove2me | solution 1 for PebblingLean.Pebbling.replaceFiber_move_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:47.725195+00:00
-- url     : https://prove2.me/submissions/76b0a3fe-e540-4540-b8c8-49564dd04ffb

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
    {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hmove : Move G E F) :
    Move (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  rcases hmove with ⟨u, v, huv, hE, rfl⟩
  refine ⟨(u, z), (v, z), ?_, ?_, ?_⟩
  · exact Or.inl ⟨huv, rfl⟩
  · simpa [fibersDistribution, replaceFiber] using hE
  · funext p
    cases p with
    | mk x z' =>
      by_cases hz' : z' = z
      · subst z'
        by_cases hxu : x = u
        · subst x
          simp [fibersDistribution, replaceFiber, moveDistribution]
        · by_cases hxv : x = v
          · subst x
            have hvu : v ≠ u := by
              simp_all
            simp [fibersDistribution, replaceFiber, moveDistribution, hvu]
          · simp [fibersDistribution, replaceFiber, moveDistribution, hxu, hxv]
      · have hp_ne_from : (x, z') ≠ (u, z) := by
          simp_all
        have hp_ne_to : (x, z') ≠ (v, z) := by
          simp_all
        simp [fibersDistribution, replaceFiber, moveDistribution, hz', hp_ne_from, hp_ne_to]
end PebblingLean.Pebbling
