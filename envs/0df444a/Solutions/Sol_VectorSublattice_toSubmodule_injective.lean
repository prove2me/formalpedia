-- Prove2me | solution 1 for VectorSublattice.toSubmodule_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:47.100383+00:00
-- url     : https://prove2.me/submissions/95b3bb02-44c8-449d-b207-3ea01f78b786

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
theorem _root_.solution :
    Function.Injective
      (toSubmodule : VectorSublattice X → Submodule ℝ X) := by
  intro p q h
  cases p; cases q; congr
end VectorSublattice
