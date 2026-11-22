-- Prove2me | solution 1 for VectorSublattice.generated_submodule_eq_infClosure_supClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:40.201676+00:00
-- url     : https://prove2.me/submissions/c70258a1-b770-48e7-88d0-04e982b48275

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_generated_submodule_eq_supClosure_infClosure

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
namespace VectorSublattice
theorem _root_.solution (M : Submodule ℝ X) :
    (generated (M : Set X) : Set X) = infClosure (supClosure (M : Set X)) := by
  let := AddCommGroup.toDistribLattice X
  rw [infClosure_supClosure, ← supClosure_infClosure]
  exact generated_submodule_eq_supClosure_infClosure M
end VectorSublattice
