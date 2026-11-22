-- Prove2me | solution 1 for Positive.extension_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:19:04.49584+00:00
-- url     : https://prove2.me/submissions/0bcce902-c5b5-483d-a186-9c50027c6002

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
theorem _root_.solution {f : X →ₗ[ℝ] Y}
    (hext : ∀ x, 0 ≤ x → f x = τ x) :
    f = extension hτ_nn hτ_add := by
  ext x
  simp only [extension_apply]
  rw [← hext _ (posPart_nonneg _), ← hext _ (negPart_nonneg _), ← map_sub]
  congr 1; exact (posPart_sub_negPart x).symm
end Positive
