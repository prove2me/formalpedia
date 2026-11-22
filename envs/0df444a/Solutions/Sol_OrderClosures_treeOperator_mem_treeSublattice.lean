-- Prove2me | solution 1 for OrderClosures.treeOperator_mem_treeSublattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:07.128062+00:00
-- url     : https://prove2.me/submissions/221313d0-050a-459c-baee-4fd9d570cc7d

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Theorems.Thm_VectorSublattice_subset_generated


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (w : TreeCoefficients n) :
    treeOperator n w ∈ treeSublattice n := by
  classical
  apply subset_closure
  change treeOperator n w ∈
    VectorSublattice.generated (Set.range (treeFunction n))
  rw [treeOperator, Finsupp.sum]
  apply Submodule.sum_mem
  intro t ht
  exact (VectorSublattice.generated (Set.range (treeFunction n))).toSubmodule.smul_mem
    _ (VectorSublattice.subset_generated _ ⟨t, rfl⟩)
end OrderClosures
