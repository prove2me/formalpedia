-- Prove2me | solution 1 for PebblingLean.Pebbling.sum_ite_nonzero_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:30.52696+00:00
-- url     : https://prove2.me/submissions/5e7f1f32-ea65-49c0-807d-d166e7f43b2d

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] (D : Pebbling V) (K : ℕ) :
    (∑ v : V, if D v = 0 then 0 else K) = supportSize D * K := by
  classical
  calc
    (∑ v : V, if D v = 0 then 0 else K)
        = ∑ v : V, if D v ≠ 0 then K else 0 := by
          simp_all
    _ = ∑ v ∈ (Finset.univ.filter fun v : V => D v ≠ 0), K := by
          rw [Finset.sum_filter]
    _ = supportSize D * K := by
          simp [supportSize, Finset.sum_const]
end PebblingLean.Pebbling
