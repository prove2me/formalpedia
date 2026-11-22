-- Prove2me | solution 1 for PebblingLean.Pebbling.size_fibersDistribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:49:32.490252+00:00
-- url     : https://prove2.me/submissions/dc65f741-d95e-4a4e-bac9-9b8353447bd7

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero


attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [Fintype W] (F : W → Pebbling V) :
    size (fibersDistribution F) = ∑ z, size (F z) := by
  classical
  rw [size]
  change (∑ p : V × W, F p.2 p.1) = ∑ z : W, size (F z)
  rw [Fintype.sum_prod_type_right]
  simp [size]
end PebblingLean.Pebbling
