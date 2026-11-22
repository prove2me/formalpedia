-- Prove2me | solution 1 for Positive.extension_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:29.660077+00:00
-- url     : https://prove2.me/submissions/00c3958a-13a7-4769-ac02-88db91680048

module
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Operators_Positive
public import Theorems.Thm_Positive_extension_apply
attribute [local simp] Positive.extension_apply

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
theorem _root_.solution {x : X} (hx : 0 ≤ x) :
    extension hτ_nn hτ_add x = τ x := by
  rw [extension_apply, posPart_of_nonneg hx, negPart_of_nonneg hx,
    tau_zero hτ_add, sub_zero]
end Positive
