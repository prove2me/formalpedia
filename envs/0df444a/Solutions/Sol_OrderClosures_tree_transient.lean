-- Prove2me | solution 1 for OrderClosures.tree_transient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:47.562132+00:00
-- url     : https://prove2.me/submissions/73c257e6-ee3a-4791-9e8e-5cefc8bea808

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Bands
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Theorems.Thm_OrderClosures_treeOperator_apply_eq_zero_of_outside_support
public import Theorems.Thm_LLexpr_NormalForm_eval_add
public import Theorems.Thm_LLexpr_NormalForm_eval_inf
public import Theorems.Thm_LLexpr_NormalForm_eval_negate
public import Theorems.Thm_LLexpr_NormalForm_eval_smul
public import Theorems.Thm_LLexpr_NormalForm_eval_sup
public import Theorems.Thm_LLexpr_NormalForm_eval_var
public import Theorems.Thm_LLexpr_NormalForm_eval_zero
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_add
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_singleton
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_smul
public import Theorems.Thm_LLexpr_SupLinearCombination_eval_sup
public import Theorems.Thm_LLexpr_eval_add
public import Theorems.Thm_LLexpr_eval_inf
public import Theorems.Thm_LLexpr_eval_reindexExpr
public import Theorems.Thm_LLexpr_eval_smul
public import Theorems.Thm_LLexpr_eval_sup
public import Theorems.Thm_LLexpr_eval_var
public import Theorems.Thm_LLexpr_eval_zero
public import Theorems.Thm_LLexpr_normalize_eval
public import Theorems.Thm_OrderClosures_commonLower_le_zero_of_parentDisjoint_subseq
public import Theorems.Thm_OrderClosures_finiteBandProjection_apply
public import Theorems.Thm_OrderClosures_treeBandProjection_support_nonempty_iff
public import Theorems.Thm_Positive_extension_apply
public import Theorems.Thm_VectorSublattice_coe_toSubmodule
public import Theorems.Thm_VectorSublattice_mem_bot
public import Theorems.Thm_VectorSublattice_mem_top
public import Theorems.Thm_coe_toCompletionVecLatHom
attribute [local simp] LLexpr.NormalForm.eval_add
attribute [local simp] LLexpr.NormalForm.eval_inf
attribute [local simp] LLexpr.NormalForm.eval_negate
attribute [local simp] LLexpr.NormalForm.eval_smul
attribute [local simp] LLexpr.NormalForm.eval_sup
attribute [local simp] LLexpr.NormalForm.eval_var
attribute [local simp] LLexpr.NormalForm.eval_zero
attribute [local simp] LLexpr.SupLinearCombination.eval_add
attribute [local simp] LLexpr.SupLinearCombination.eval_singleton
attribute [local simp] LLexpr.SupLinearCombination.eval_smul
attribute [local simp] LLexpr.SupLinearCombination.eval_sup
attribute [local simp] LLexpr.eval_add
attribute [local simp] LLexpr.eval_inf
attribute [local simp] LLexpr.eval_reindexExpr
attribute [local simp] LLexpr.eval_smul
attribute [local simp] LLexpr.eval_sup
attribute [local simp] LLexpr.eval_var
attribute [local simp] LLexpr.eval_zero
attribute [local simp] LLexpr.normalize_eval
attribute [local simp] Positive.extension_apply
attribute [local simp] VectorSublattice.coe_toSubmodule
attribute [local simp] VectorSublattice.mem_bot
attribute [local simp] VectorSublattice.mem_top
attribute [local simp] coe_toCompletionVecLatHom



set_option autoImplicit true
@[expose] public section
public section
open OrderClosures
open Set Filter Topology
open scoped NNReal Topology
universe u
namespace OrderClosures
theorem _root_.solution
    (n : ℕ) (w : ℕ → TreeCoefficients n) (Λ : Finset (TreeBandIndex n))
    (hnone : none ∈ Λ)
    (hdis : ∀ B ∉ Λ,
      {m | (treeBandProjection n B (w m)).support.Nonempty}.Subsingleton) :
    let v := fun m ↦ w m - finiteBandProjection n Λ (w m)
    (Pairwise fun i j ↦ ParentDisjoint ((v i).support : Set (TreeNode n))
      ((v j).support : Set (TreeNode n))) ∧
    ∀ z : BoundedContinuousFunction (TreeProduct n) ℝ,
      0 ≤ z → (∀ m, z ≤ treeOperator n (v m)) → z = 0 := by
  classical
  dsimp
  let v : ℕ → TreeCoefficients n := fun m ↦
    w m - finiteBandProjection n Λ (w m)
  have hv_apply (m : ℕ) (t : TreeNode n) :
      v m t = if treeBandOfNode n t ∈ Λ then 0 else w m t := by
    change (w m - finiteBandProjection n Λ (w m)) t = _
    rw [Finsupp.sub_apply]
    by_cases hB : treeBandOfNode n t ∈ Λ
    · rw [(finiteBandProjection_apply n Λ (w m) t).1 hB]
      simp [hB]
    · rw [(finiteBandProjection_apply n Λ (w m) t).2 hB]
      simp [hB]
  have hv_band_notMem {m : ℕ} {t : TreeNode n} (ht : t ∈ (v m).support) :
      treeBandOfNode n t ∉ Λ := by
    intro hB
    have htne := Finsupp.mem_support_iff.mp ht
    rw [hv_apply, if_pos hB] at htne
    exact htne rfl
  have hv_root_notMem (m : ℕ) : TreeNode.root n ∉ (v m).support := by
    intro ht
    have hB := hv_band_notMem ht
    apply hB
    simpa [treeBandOfNode] using hnone
  have hpair : Pairwise fun i j ↦
      ParentDisjoint ((v i).support : Set (TreeNode n))
        ((v j).support : Set (TreeNode n)) := by
    intro i j hij
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    rcases hq.1 with ⟨ti, hti, hpti⟩
    rcases hq.2 with ⟨tj, htj, hptj⟩
    have htiroot : ti ≠ TreeNode.root n := fun h ↦ hv_root_notMem i (h ▸ hti)
    have htjroot : tj ≠ TreeNode.root n := fun h ↦ hv_root_notMem j (h ▸ htj)
    let B := treeBandOfNode n ti
    have hBnot : B ∉ Λ := hv_band_notMem hti
    have hBsame : treeBandOfNode n tj = B := by
      change treeBandOfNode n tj = treeBandOfNode n ti
      rw [treeBandOfNode, dif_neg htjroot, treeBandOfNode, dif_neg htiroot]
      congr 2
      exact hptj.trans hpti.symm
    have hwti : ti ∈ (w i).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp hti
      rw [hv_apply, if_neg hBnot] at hvne
      exact hvne
    have hBt_i : (treeBandProjection n B (w i)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w i)).mpr
        ⟨ti, hwti, rfl⟩
    have hwjt : tj ∈ (w j).support := by
      rw [Finsupp.mem_support_iff]
      have hvne := Finsupp.mem_support_iff.mp htj
      rw [hv_apply, if_neg (hBsame ▸ hBnot)] at hvne
      exact hvne
    have hBt_j : (treeBandProjection n B (w j)).support.Nonempty :=
      (treeBandProjection_support_nonempty_iff n B (w j)).mpr
        ⟨tj, hwjt, hBsame⟩
    exact hij ((hdis B hBnot) hBt_i hBt_j)
  refine ⟨hpair, ?_⟩
  intro z hzpos hzlower
  apply le_antisymm
  · exact commonLower_le_zero_of_parentDisjoint_subseq n
      (fun m ↦ (v m).support) hpair id Function.injective_id hv_root_notMem
      (fun m ↦ treeOperator n (v m))
      (fun m α hα ↦ treeOperator_apply_eq_zero_of_outside_support n (v m) hα)
      hzlower
  · exact hzpos
end OrderClosures
