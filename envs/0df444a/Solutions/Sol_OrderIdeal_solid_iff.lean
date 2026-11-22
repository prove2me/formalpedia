-- Prove2me | solution 1 for OrderIdeal.solid_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:27:41.842904+00:00
-- url     : https://prove2.me/submissions/1a9dfbd4-136f-4668-8cbd-c3cf6ba49629

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
namespace OrderIdeal
theorem _root_.solution (M : Submodule ℝ X) :
    (∀ x y : X, x ∈ M → |y| ≤ |x| → y ∈ M) ↔
      (∀ x y : X, x ∈ M → 0 ≤ y → y ≤ x → y ∈ M) ∧
        ∀ x y : X, x ∈ M → y ∈ M → x ⊔ y ∈ M := by
  constructor
  · intro h
    exact ⟨fun _ _ hx hy0 hyx => (ofSolid M h).solid' hx hy0 hyx,
           fun _ _ hx hy => (ofSolid M h).sup_mem' hx hy⟩
  · intro ⟨hsol, hsup⟩ x y hx hle
    -- |x| ∈ M
    have habs_x : |x| ∈ M := hsup x (-x) hx (M.neg_mem hx)
    -- |y| ∈ M by solidity: 0 ≤ |y| ≤ |x| and |x| ∈ M
    have habs_y : |y| ∈ M := hsol (|x|) (|y|) habs_x (abs_nonneg y) hle
    -- y⁺ ∈ M: 0 ≤ y⁺ ≤ |y|
    have hpos : y⁺ ∈ M :=
      hsol (|y|) y⁺ habs_y (posPart_nonneg y) (sup_le (le_abs_self y) (abs_nonneg y))
    -- y⁻ ∈ M: 0 ≤ y⁻ ≤ |y|
    have hneg : y⁻ ∈ M :=
      hsol (|y|) y⁻ habs_y (negPart_nonneg y) (sup_le (neg_le_abs y) (abs_nonneg y))
    have := M.sub_mem hpos hneg
    rwa [posPart_sub_negPart] at this
end OrderIdeal
