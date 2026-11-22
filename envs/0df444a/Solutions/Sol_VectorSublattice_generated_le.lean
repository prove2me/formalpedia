-- Prove2me | solution 1 for VectorSublattice.generated_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:49.31628+00:00
-- url     : https://prove2.me/submissions/5bf5f40b-5ae4-4de9-a4a3-2a0a481117a5

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
theorem _root_.solution {s : Set X} {Y : VectorSublattice X} (h : s ⊆ Y) :
    generated s ≤ Y := by
  intro x hx
  have := (Submodule.mem_sInf).mp hx
  exact this _ ⟨Y, h, rfl⟩
end VectorSublattice
