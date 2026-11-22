-- Prove2me | solution 1 for OrderIdeal.exists_sum_decomp_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:28:09.766374+00:00
-- url     : https://prove2.me/submissions/7514fc94-3b8d-46ce-b54c-e888f54756ac

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderUnit
public import Mathlib.Analysis.Normed.Group.Completeness
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Ideal
public import Theorems.Thm_VectorSublattice_abs_mem


set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open OrderIdeal
variable (J : OrderIdeal X)
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
variable (a : X)
namespace OrderIdeal
theorem _root_.solution (J₁ J₂ : OrderIdeal X) {y : X}
    (hy : y ∈ J₁.toSubmodule + J₂.toSubmodule) (hy0 : 0 ≤ y) :
    ∃ y₁ y₂ : X, y₁ ∈ J₁ ∧ y₂ ∈ J₂ ∧ y₁ + y₂ = y ∧ 0 ≤ y₁ ∧ 0 ≤ y₂ := by
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hy
  have hau₁ : |u₁| ∈ J₁ := J₁.abs_mem hu₁
  have hau₂ : |u₂| ∈ J₂ := J₂.abs_mem hu₂
  have hau₁_nn : 0 ≤ |u₁| := abs_nonneg _
  have hau₂_nn : 0 ≤ |u₂| := abs_nonneg _
  have hyle : u₁ + u₂ ≤ |u₁| + |u₂| :=
    add_le_add (le_abs_self u₁) (le_abs_self u₂)
  refine ⟨(u₁ + u₂) ⊓ |u₁|, (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁|,
    J₁.solid hau₁ (le_inf hy0 hau₁_nn) inf_le_right,
    ?_, by abel, le_inf hy0 hau₁_nn, ?_⟩
  · have heq : (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁| = ((u₁ + u₂) - |u₁|)⁺ := by
      rw [inf_eq_sub_posPart_sub]; abel
    rw [heq]
    exact J₂.solid hau₂ (posPart_nonneg _)
      (sup_le (sub_le_iff_le_add'.mpr hyle) hau₂_nn)
  · have heq : (u₁ + u₂) - (u₁ + u₂) ⊓ |u₁| = ((u₁ + u₂) - |u₁|)⁺ := by
      rw [inf_eq_sub_posPart_sub]; abel
    rw [heq]; exact posPart_nonneg _
end OrderIdeal
