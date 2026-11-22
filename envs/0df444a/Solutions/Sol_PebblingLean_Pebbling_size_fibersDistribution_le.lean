-- Prove2me | solution 1 for PebblingLean.Pebbling.size_fibersDistribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:11.451363+00:00
-- url     : https://prove2.me/submissions/a97f4372-111a-4936-8da2-115b50fc4cad

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_size_fibersDistribution

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [Fintype V] [Fintype W] {F : W → Pebbling V}
    {cost : W → ℕ} (hcost : ∀ z : W, size (F z) ≤ cost z) :
    size (fibersDistribution F) ≤ ∑ z, cost z := by
  classical
  rw [size_fibersDistribution]
  exact Finset.sum_le_sum fun z _ => hcost z
end PebblingLean.Pebbling
