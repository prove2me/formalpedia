-- Prove2me | solution 1 for PebblingLean.Pebbling.hasSolvableAtMostSize_product_of_fiber_demands
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:04:58.983971+00:00
-- url     : https://prove2.me/submissions/3bca3689-8c45-4b05-b13c-fe557430a6a4

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_size_fibersDistribution_le
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_solvable_product_of_fiber_demands
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_zero
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
theorem _root_.solution
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E : Pebbling W} {cost : W → ℕ}
    (hE : Solvable H E)
    (hcost : ∀ z : W, E z ≠ 0 → HasSolvableAtMostSize G (E z) (cost z)) :
    HasSolvableAtMostSize (Graph.cartesianProduct G H) 1
      (∑ z, if E z = 0 then 0 else cost z) := by
  classical
  let F : W → Pebbling V := fun z =>
    if hz : E z = 0 then (fun _ : V => 0) else Classical.choose (hcost z hz)
  have hFsolv : ∀ z : W, SolvableAtLeast G (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · rw [hz]
      exact solvableAtLeast_zero G (F z)
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).2
  have hFsize : ∀ z : W, size (F z) ≤ if E z = 0 then 0 else cost z := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · simpa [F, hz] using (Classical.choose_spec (hcost z hz)).1
  refine ⟨fibersDistribution F, ?_, ?_⟩
  · exact size_fibersDistribution_le hFsize
  · exact solvable_product_of_fiber_demands (G := G) (H := H) hE hFsolv
end PebblingLean.Pebbling
