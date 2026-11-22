-- Prove2me | solution 1 for VecLatHom.isVecLatHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:24:57.531339+00:00
-- url     : https://prove2.me/submissions/1c5fd11c-fd6a-413e-81f0-b56b55c3fdec

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
theorem _root_.solution (f : VecLatHom X Y) : IsVecLatHom f where
  map_add := f.toLinearMap.map_add
  map_smul := f.toLinearMap.map_smul
  map_sup' := f.toLatticeHom.map_sup'
  map_inf' := f.toLatticeHom.map_inf'
end VecLatHom
