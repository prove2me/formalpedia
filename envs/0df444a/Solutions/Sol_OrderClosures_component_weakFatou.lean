-- Prove2me | solution 1 for OrderClosures.component_weakFatou
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:58.340882+00:00
-- url     : https://prove2.me/submissions/3b780d7f-54e8-4558-aee7-99ceb0633264

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Theorems.Thm_OrderClosures_component_moderated
public import Theorems.Thm_OrderClosures_treeOperator_mem_treeSublattice
public import Theorems.Thm_OrderClosures_weakFatou_of_weakNakano_p
public import Theorems.Thm_OrderClosures_weakNakano_of_weakSequentialNakano_p
public import Theorems.Thm_VectorSublattice_separableSpace_topologicalClosure_generated_of_countable


set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution (n : ℕ) :
    IsWeakNakanoConstant (componentLatticeNorm n) 2 ∧
      HasWeakFatouProperty (componentLatticeNorm n) 2 := by
  have hseq : IsWeakSequentialNakanoConstant (componentLatticeNorm n) 2 := by
    refine ⟨by norm_num, ?_⟩
    intro x hxmono hxpos _ hxnorm ε hε
    obtain ⟨w, hw, hwupper, hwrho⟩ :=
      component_moderated n x hxmono hxpos hxnorm hε
    let y : TreeComponent n := ⟨treeOperator n w, treeOperator_mem_treeSublattice n w⟩
    refine ⟨y, ?_, ?_, ?_⟩
    · exact treeOperator_nonneg n w hw
    · exact hwupper
    · change treeSeminorm n (treeOperator n w) ≤ 2 + ε
      apply (treeSeminorm_le_of_majorant n (treeOperator n w) w hw ?_).trans hwrho
      rw [abs_of_nonneg (treeOperator_nonneg n w hw)]
  let : Countable (TreeNode n) := by
    unfold TreeNode
    infer_instance
  let : TopologicalSpace.SeparableSpace (TreeComponent n) :=
    VectorSublattice.separableSpace_topologicalClosure_generated_of_countable
      (Set.countable_range (treeFunction n))
  have hNak : IsWeakNakanoConstant (componentLatticeNorm n) 2 :=
    weakNakano_of_weakSequentialNakano_p (Y := TreeComponent n) (K := 2)
      (componentLatticeNorm n) hseq
  exact ⟨hNak, weakFatou_of_weakNakano_p (componentLatticeNorm n) hNak⟩
end OrderClosures
