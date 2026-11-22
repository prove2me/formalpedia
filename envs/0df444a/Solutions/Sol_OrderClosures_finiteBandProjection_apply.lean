-- Prove2me | solution 1 for OrderClosures.finiteBandProjection_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:18.667843+00:00
-- url     : https://prove2.me/submissions/062a395d-9e68-4aa6-8f30-bada2c459a9f

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
theorem _root_.solution (n : ℕ) (Λ : Finset (TreeBandIndex n))
    (w : TreeCoefficients n) (t : TreeNode n) :
    (treeBandOfNode n t ∈ Λ → finiteBandProjection n Λ w t = w t) ∧
      (treeBandOfNode n t ∉ Λ → finiteBandProjection n Λ w t = 0) := by
  classical
  constructor
  · intro hB
    apply Finsupp.filter_apply_pos
    exact ⟨treeBandOfNode n t, hB, node_mem_its_treeBand n t⟩
  · intro hB
    apply Finsupp.filter_apply_neg
    rintro ⟨B, hBΛ, htB⟩
    exact hB (treeBandOfNode_eq_of_mem n t B htB ▸ hBΛ)
end OrderClosures
