-- Prove2me | solution 1 for Positive.extension_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:21.875798+00:00
-- url     : https://prove2.me/submissions/6971d5e7-2fa5-45d0-bb50-f98a787f23af

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Theorems.Thm_Positive_extension_nonneg

set_option autoImplicit true
@[expose] public section
public section
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
open Positive
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Lattice X] [Lattice Y]
  [IsOrderedAddMonoid X] [IsOrderedAddMonoid Y] [VectorLattice X] [VectorLattice Y]
  [IsVLArchimedean Y] {τ : X → Y}
variable
  (hτ_nn : ∀ x, 0 ≤ x → 0 ≤ τ x)
  (hτ_add : ∀ x y, 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y)
namespace Positive
theorem _root_.solution : Positive (extension hτ_nn hτ_add) :=
  fun x hx => by
    rw [extension_nonneg hτ_nn hτ_add hx]; exact hτ_nn _ hx
end Positive
