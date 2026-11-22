-- Prove2me | solution 1 for VecLatHom.map_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:11.061906+00:00
-- url     : https://prove2.me/submissions/67015e4b-23f9-485b-9425-2c967203ee1f

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
theorem _root_.solution (f : VecLatHom X Y) {x : X} (hx : 0 ≤ x) : 0 ≤ f x := by
  have h := f.monotone hx; rwa [map_zero] at h
end VecLatHom
