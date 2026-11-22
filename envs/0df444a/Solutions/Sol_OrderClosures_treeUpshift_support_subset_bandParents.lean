-- Prove2me | solution 1 for OrderClosures.treeUpshift_support_subset_bandParents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:42.215326+00:00
-- url     : https://prove2.me/submissions/f46e5f31-64fb-4edf-82ac-1b61cde9cdc7

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_finiteBandProjection_apply
public import Theorems.Thm_OrderClosures_parent_eq_treeBandParent

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ)
    (Λ : Finset (TreeBandIndex n)) (w : TreeCoefficients n) :
    (treeUpshift n (finiteBandProjection n Λ w)).support ⊆
      treeBandParents n Λ := by
  classical
  intro q hq
  rw [treeUpshift] at hq
  have hq' := Finsupp.mapDomain_support hq
  rcases Finset.mem_image.mp hq' with ⟨t, ht, rfl⟩
  rw [treeBandParents]
  apply Finset.mem_image.mpr
  refine ⟨treeBandOfNode n t, ?_, (parent_eq_treeBandParent n t).symm⟩
  have htfinite : t ∈ (finiteBandProjection n Λ w).support := ht
  by_contra hnot
  have hzero := (finiteBandProjection_apply n Λ w t).2 hnot
  exact Finsupp.mem_support_iff.mp htfinite hzero
end OrderClosures
