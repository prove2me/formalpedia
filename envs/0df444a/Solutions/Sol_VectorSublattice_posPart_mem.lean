-- Prove2me | solution 1 for VectorSublattice.posPart_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:07.959723+00:00
-- url     : https://prove2.me/submissions/b5178c0b-4b5a-4256-aa0c-65daffc69160

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
theorem _root_.solution {x : X} (hx : x ∈ Y) : x⁺ ∈ Y :=
  Y.sup_mem' hx (Y.toSubmodule.zero_mem)
end VectorSublattice
