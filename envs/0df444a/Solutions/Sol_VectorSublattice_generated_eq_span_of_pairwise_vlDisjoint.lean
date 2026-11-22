-- Prove2me | solution 1 for VectorSublattice.generated_eq_span_of_pairwise_vlDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:25:39.678687+00:00
-- url     : https://prove2.me/submissions/a1a1f3b1-0de8-4231-8d70-e393c218503e

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_LLexpr
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Order.Sublattice
public import Mathlib.Order.SupClosed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Substructures_Sublattice
public import Theorems.Thm_VectorSublattice_subset_generated
public import Theorems.Thm_VectorSublattice_generated_le
public import Theorems.Thm_abs_sum_finset

section
@[expose] public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace PointedCone
end PointedCone
namespace VectorSublattice
variable (Y : VectorSublattice X)
private lemma abs_sum_finset_of_pairwise_vlDisjoint {s : Finset X} {f : X → ℝ}
    (hdisj : (s : Set X).Pairwise IsVLDisjoint) :
    |∑ a ∈ s, f a • a| = ∑ a ∈ s, |f a| • |a| := by
  exact abs_sum_finset s id f hdisj
end VectorSublattice
namespace LLexpr
variable {n : ℕ}
section Combinations
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
end Combinations
end LLexpr
section Normed
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [NormedVectorLattice X]
namespace VectorSublattice
variable (Y : VectorSublattice X)
end VectorSublattice
end Normed
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
open VectorSublattice
variable (Y : VectorSublattice X)
namespace VectorSublattice
theorem _root_.solution {A : Set X}
    (hA : A.Pairwise IsVLDisjoint) (hA_nn : ∀ a ∈ A, 0 ≤ a) :
    (generated A).toSubmodule = Submodule.span ℝ A := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (subset_generated A))
  have h_abs : ∀ u, u ∈ Submodule.span ℝ A → |u| ∈ Submodule.span ℝ A := by
    intro u hu
    obtain ⟨f, t, ht_sub, _, hsum⟩ :=
      Submodule.mem_span_iff_exists_finset_subset.mp hu
    have hdisj_t : (t : Set X).Pairwise IsVLDisjoint := fun i hi j hj hij =>
      hA (ht_sub hi) (ht_sub hj) hij
    have hnn_t : ∀ a ∈ t, 0 ≤ a := fun a ha => hA_nn a (ht_sub ha)
    rw [← hsum, abs_sum_finset_of_pairwise_vlDisjoint hdisj_t]
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [abs_of_nonneg (hnn_t a ha)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (ht_sub ha))
  let Y : VectorSublattice X := ofAbsClosed (Submodule.span ℝ A) h_abs
  have hA_sub : A ⊆ (Y : Set X) := Submodule.subset_span
  have hle := generated_le (Y := Y) hA_sub
  intro x hx
  exact hle hx
end VectorSublattice
