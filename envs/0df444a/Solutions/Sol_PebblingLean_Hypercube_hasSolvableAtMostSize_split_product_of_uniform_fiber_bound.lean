-- Prove2me | solution 1 for PebblingLean.Hypercube.hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:06:49.964666+00:00
-- url     : https://prove2.me/submissions/06ec6595-3293-475b-b787-00ef6434e82d

module
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finite.Prod
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_HypercubeProduct
public import Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_split_product_of_fiber_demands
public import Theorems.Thm_PebblingLean_Hypercube_mem_annulus
public import Theorems.Thm_PebblingLean_Pebbling_fibersDistribution_apply
public import Theorems.Thm_PebblingLean_Pebbling_hasSolvableAtMostSize_mono_demand
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_off
public import Theorems.Thm_PebblingLean_Pebbling_sliceDistribution_apply_on
public import Theorems.Thm_PebblingLean_Pebbling_solvable_of_solvableAtLeast
public import Theorems.Thm_PebblingLean_Pebbling_sum_ite_nonzero_const
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
    {a m Tbase Tfiber K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber K) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.supportSize E * K) := by
  classical
  have hprod :=
    hasSolvableAtMostSize_split_product_of_fiber_demands
      (a := a) (m := m) (E := E)
      (cost := fun _z : HypercubeVertex m => K)
      (Pebbling.solvable_of_solvableAtLeast hTbase hE)
      (fun z _hz =>
        Pebbling.hasSolvableAtMostSize_mono_demand (hpile_le z) hfiber)
  simpa [Pebbling.sum_ite_nonzero_const] using hprod
end PebblingLean.Hypercube
