-- Prove2me | solution 1 for VecLatHom.map_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:58.146259+00:00
-- url     : https://prove2.me/submissions/e53a2468-a5d1-4b9c-9cf8-06845e2d70a9

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
theorem _root_.solution (f : VecLatHom X Y) (x : X) : f |x| = |f x| := by
  rw [abs, abs, map_sup, map_neg]
end VecLatHom
