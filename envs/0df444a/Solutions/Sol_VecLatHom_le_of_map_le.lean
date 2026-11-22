-- Prove2me | solution 1 for VecLatHom.le_of_map_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:11.791838+00:00
-- url     : https://prove2.me/submissions/1036a760-e39f-4125-802a-19f2aa5ef429

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
theorem _root_.solution (f : VecLatHom X Y) (hf : Function.Injective f) {a b : X}
    (hab : f a ≤ f b) : a ≤ b :=
  sup_eq_right.mp (hf (by rw [map_sup f a b]; exact sup_eq_right.mpr hab))
end VecLatHom
