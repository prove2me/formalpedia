-- Prove2me | solution 1 for OrderClosures.treeRho_finiteBandProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:12.005028+00:00
-- url     : https://prove2.me/submissions/04c76865-17e0-4fa7-8d14-152b51b90af3

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_node_mem_its_treeBand
public import Theorems.Thm_OrderClosures_treeBandOfNode_eq_of_mem

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
    treeRho n (finiteBandProjection n Λ w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (finiteBandProjection n Λ w) =
      ∑ t ∈ w.support.filter (fun t ↦ treeBandOfNode n t ∈ Λ),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    have hp (t : TreeNode n) :
        (∃ B ∈ Λ, t ∈ treeBandSupport n B) ↔ treeBandOfNode n t ∈ Λ := by
      constructor
      · rintro ⟨B, hB, ht⟩
        exact treeBandOfNode_eq_of_mem n t B ht ▸ hB
      · intro ht
        exact ⟨treeBandOfNode n t, ht, node_mem_its_treeBand n t⟩
    rw [treeRho, finiteBandProjection, Finsupp.sum, Finsupp.support_filter]
    simp_rw [hp]
    apply Finset.sum_congr rfl
    intro t ht
    have happly : (w.filter fun x ↦ treeBandOfNode n x ∈ Λ) t = w t :=
      Finsupp.filter_apply_pos (fun x ↦ treeBandOfNode n x ∈ Λ) w
        (Finset.mem_filter.mp ht).2
    rw [happly]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
end OrderClosures
