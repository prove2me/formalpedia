-- Prove2me | solution 1 for Positive.le_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:16:01.519252+00:00
-- url     : https://prove2.me/submissions/e00fc5fd-a7bd-4c63-9237-e316b9a648d7

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive

set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive
namespace Positive
theorem _root_.solution {T S : X →ₗ[ℝ] Y} : T ≤ S ↔ Positive (S - T) := Iff.rfl
end Positive
