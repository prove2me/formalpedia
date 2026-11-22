-- Prove2me | solution 1 for Positive.monotone_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:31.701631+00:00
-- url     : https://prove2.me/submissions/1760fff9-2b77-473d-91fd-d9d75745c5a4

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
theorem _root_.solution {f : X →ₗ[ℝ] Y} : Monotone f ↔ Positive f := by
  constructor
  · intro hm x hx
    simpa [map_zero] using hm hx
  · intro hp a b hab
    have h : 0 ≤ f (b - a) := hp (b - a) (sub_nonneg.mpr hab)
    rwa [map_sub, sub_nonneg] at h
end Positive
