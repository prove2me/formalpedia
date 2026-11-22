-- Prove2me | solution 1 for OrderClosures.treeRho_bandProjection_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:17.201516+00:00
-- url     : https://prove2.me/submissions/75532a40-a264-464c-8706-54c201cab5bf

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands

set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (B : TreeBandIndex n)
    (w : TreeCoefficients n) :
    treeRho n (treeBandProjection n B w) ≤ treeRho n w := by
  classical
  have heq : treeRho n (treeBandProjection n B w) =
      ∑ t ∈ w.support.filter (fun t ↦ t ∈ treeBandSupport n B),
        (2 : ℝ) ^ (-(TreeNode.level t : ℤ)) * |w t| := by
    rw [treeRho, treeBandProjection, Finsupp.sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finsupp.filter_apply_pos _ _ (Finset.mem_filter.mp ht).2]
  rw [heq, treeRho, Finsupp.sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro t _ _
  exact mul_nonneg (zpow_nonneg (by norm_num) _) (abs_nonneg _)
end OrderClosures
