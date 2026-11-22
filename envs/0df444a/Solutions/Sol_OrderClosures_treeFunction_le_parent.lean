-- Prove2me | solution 1 for OrderClosures.treeFunction_le_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:15.043649+00:00
-- url     : https://prove2.me/submissions/aaf7fd93-410f-4aa6-8f28-e2f2cd88018d

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Theorems.Thm_OrderClosures_treeCylinder_subset_parent
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem
public import Theorems.Thm_OrderClosures_treeFunction_nonneg


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (t : TreeNode n) :
    treeFunction n t ≤ treeFunction n (TreeNode.parent t) := by
  intro α
  change treeFunction n t α ≤ treeFunction n (TreeNode.parent t) α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα,
      treeFunction_apply_of_mem n _ (treeCylinder_subset_parent n t hα)]
  · rw [treeFunction_apply_of_notMem n t hα]
    exact treeFunction_nonneg n _ α
end OrderClosures
