-- Prove2me | solution 1 for PebblingLean.Pebbling.supportSize_mul_le_size_of_minOccupiedPileSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:37.248808+00:00
-- url     : https://prove2.me/submissions/bce39553-b398-4f1f-9e29-7d74453e7075

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_sum_ite_nonzero_const
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
theorem _root_.solution [Fintype V]
    {D : Pebbling V} {S : ℕ} (hmin : MinOccupiedPileSize D S) :
    supportSize D * S ≤ size D := by
  classical
  have hsum :
      (∑ v : V, if D v = 0 then 0 else S) ≤ ∑ v : V, D v := by
    refine Finset.sum_le_sum ?_
    intro v _hv
    by_cases hv0 : D v = 0
    · simp [hv0]
    · simpa [hv0] using hmin v hv0
  simpa [sum_ite_nonzero_const, size] using hsum
end PebblingLean.Pebbling
