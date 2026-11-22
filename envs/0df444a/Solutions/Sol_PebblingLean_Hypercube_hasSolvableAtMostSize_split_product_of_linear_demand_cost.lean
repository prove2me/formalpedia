-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_linear_demand_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:05.123821+00:00
-- url     : https://prove2.me/submissions/e7271ef2-471f-4340-a233-289fb4145dff

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_demand_cost
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
attribute [local simp] PebblingLean.Hypercube.mem_annulus
attribute [local simp] PebblingLean.Pebbling.fibersDistribution_apply
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_off
attribute [local simp] PebblingLean.Pebbling.sliceDistribution_apply_on



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {a m K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ,
        Pebbling.HasSolvableAtMostSize (graph a) T (K * T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (K * Pebbling.size E) := by
  classical
  have hprod :=
    hasSolvableAtMostSize_split_product_of_demand_cost
      (a := a) (m := m) (E := E)
      (demandCost := fun T : ℕ => K * T)
      hE (fun T _hT => hcost T)
  have hsum :
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else K * E z) =
        K * Pebbling.size E := by
    rw [Pebbling.size, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    simp_all
  simpa [hsum] using hprod
end PebblingLean.Hypercube
