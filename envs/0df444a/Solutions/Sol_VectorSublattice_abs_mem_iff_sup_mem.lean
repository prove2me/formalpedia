-- Prove2me | solution 1 for VectorSublattice.abs_mem_iff_sup_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:08.49427+00:00
-- url     : https://prove2.me/submissions/2c20c3e8-9d0f-4c47-807c-e144b7bb0191

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
theorem _root_.solution (M : Submodule ℝ X) :
    (∀ x : X, x ∈ M → |x| ∈ M) ↔
      ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by
  constructor
  · intro h x y hx hy
    exact (ofAbsClosed M h).sup_mem' hx hy
  · intro h x hx
    exact h x (-x) hx (M.neg_mem hx)
end VectorSublattice
