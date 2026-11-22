-- Prove2me | solution 1 for VectorSublattice.subset_generated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:24.354842+00:00
-- url     : https://prove2.me/submissions/85ab99b5-12b2-4a4a-9a32-e1d98eef698a

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
namespace VectorSublattice
theorem _root_.solution (s : Set X) : s ⊆ (generated s : Set X) := by
  intro x hx
  refine (Submodule.mem_sInf).mpr ?_
  rintro _ ⟨Y, hY, rfl⟩
  exact hY hx
end VectorSublattice
