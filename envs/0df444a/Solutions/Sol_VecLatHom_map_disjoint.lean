-- Prove2me | solution 1 for VecLatHom.map_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:20.010141+00:00
-- url     : https://prove2.me/submissions/46d2480e-9f50-4e9c-be0d-219b4a25b9de

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Hom

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} {Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  [Lattice X] [Lattice Y] [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y]
  [VectorLattice X] [VectorLattice Y]
open VecLatHom
namespace VecLatHom
theorem _root_.solution (f : VecLatHom X Y) {x y : X} (h : x ⊓ y = 0) : f x ⊓ f y = 0 := by
  rw [← map_inf, h, map_zero]
end VecLatHom
