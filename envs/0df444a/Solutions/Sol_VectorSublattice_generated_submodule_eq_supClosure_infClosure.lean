-- Prove2me | solution 1 for VectorSublattice.generated_submodule_eq_supClosure_infClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:51.17959+00:00
-- url     : https://prove2.me/submissions/198265e5-7eac-4c60-8e15-93edb5738e40

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_isSublattice
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
namespace VectorSublattice
theorem _root_.solution (M : Submodule ℝ X) :
    (generated (M : Set X) : Set X) = supClosure (infClosure (M : Set X)) := by
  let := AddCommGroup.toDistribLattice X
  rw [supClosure_infClosure]
  refine Set.Subset.antisymm ?_ ?_
  · have h : (M : Set X) ⊆ (sublatticeOfSubmoduleLatticeClosure M : Set X) :=
      fun _ hx => subset_latticeClosure hx
    exact generated_le h
  · exact latticeClosure_min (subset_generated _)
      (generated (M : Set X)).isSublattice
end VectorSublattice
