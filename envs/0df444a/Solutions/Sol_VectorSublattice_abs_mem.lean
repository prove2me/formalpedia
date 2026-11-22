-- Prove2me | solution 1 for VectorSublattice.abs_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:40.553803+00:00
-- url     : https://prove2.me/submissions/292bd6fb-998b-42e2-959a-63325fb7cf04

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
theorem _root_.solution {x : X} (hx : x ∈ Y) : |x| ∈ Y :=
  sup_mem Y hx (Y.toSubmodule.neg_mem hx)
end VectorSublattice
