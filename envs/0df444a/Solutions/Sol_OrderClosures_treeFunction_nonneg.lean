-- Prove2me | solution 1 for OrderClosures.treeFunction_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:41.704811+00:00
-- url     : https://prove2.me/submissions/5d7cc535-882a-4216-b050-9d8fbc6db23e

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_TreeNorm
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_mem
public import Theorems.Thm_OrderClosures_treeFunction_apply_of_notMem


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) (t : TreeNode n) :
    0 ≤ treeFunction n t := by
  intro α
  change (0 : ℝ) ≤ treeFunction n t α
  by_cases hα : α ∈ treeCylinder n t
  · rw [treeFunction_apply_of_mem n t hα]
    norm_num
  · rw [treeFunction_apply_of_notMem n t hα]
end OrderClosures
