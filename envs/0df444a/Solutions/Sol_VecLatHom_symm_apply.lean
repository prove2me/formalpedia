-- Prove2me | solution 1 for VecLatHom.symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:24.080011+00:00
-- url     : https://prove2.me/submissions/c3533317-f04c-4f2c-97c8-fd207fdd30cd

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
theorem _root_.solution (f : VecLatHom X Y) (h : Function.Bijective f)
  (x : X) (y : Y) : (f.symm h) y = x ↔ y = f x := by
    let lineq := LinearEquiv.ofBijective f.toLinearMap h
    change lineq.symm y = x ↔ y = f x
    apply LinearEquiv.symm_apply_eq
end VecLatHom
