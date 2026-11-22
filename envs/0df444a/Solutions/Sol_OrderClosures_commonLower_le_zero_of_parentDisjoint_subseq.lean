-- Prove2me | solution 1 for OrderClosures.commonLower_le_zero_of_parentDisjoint_subseq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:10.852691+00:00
-- url     : https://prove2.me/submissions/ff7450c3-3d9d-4cc8-af48-86142c6677c9

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FiniteTree
public import Theorems.Thm_OrderClosures_strictPrefix_last_eq_parent
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
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_Positive_continuous
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
    (n : ℕ) (F : ℕ → Finset (TreeNode n))
    (hF : Pairwise fun i j ↦ ParentDisjoint (F i : Set (TreeNode n))
      (F j : Set (TreeNode n)))
    (φ : ℕ → ℕ) (hφ : Function.Injective φ)
    (hroot : ∀ m, TreeNode.root n ∉ F (φ m))
    (g : ℕ → BoundedContinuousFunction (TreeProduct n) ℝ)
    (hgzero : ∀ m α, α ∉ finiteCylinderUnion n (F (φ m)) → g (φ m) α = 0)
    {z : BoundedContinuousFunction (TreeProduct n) ℝ}
    (hz : ∀ m, z ≤ g m) : z ≤ 0 := by
  classical
  intro α
  change z α ≤ 0
  let β : ℕ → TreeProduct n := fun m q ↦
    max (α q) ((F (φ m)).sup fun t ↦
      if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0)
  have hβoutside : ∀ m, β m ∉ finiteCylinderUnion n (F (φ m)) := by
    intro m hmem
    simp only [finiteCylinderUnion, Set.mem_iUnion] at hmem
    obtain ⟨t, ht⟩ := hmem
    have htF : t.1 ∈ F (φ m) := t.2
    have htroot : t.1 ≠ TreeNode.root n := fun h ↦ hroot m (h ▸ htF)
    have htpos : 0 < TreeNode.level t.1 := Nat.pos_of_ne_zero fun hzero ↦ by
      apply htroot
      apply Subtype.ext
      have hnil : t.1.1 = [] := List.length_eq_zero_iff.mp (by
        simpa [TreeNode.level] using hzero)
      simpa [TreeNode.root] using hnil
    let j : Fin (TreeNode.level t.1) :=
      ⟨TreeNode.level t.1 - 1, Nat.sub_lt htpos (by omega)⟩
    have hj := strictPrefix_last_eq_parent t.1 htpos
    have hsup : treeLastLabel t.1 + 1 ≤
        (F (φ m)).sup fun u ↦
          if TreeNode.parent u = (strictPrefix t.1 j).1 then treeLastLabel u + 1 else 0 := by
      have hle := Finset.le_sup (s := F (φ m))
        (f := fun u ↦ if TreeNode.parent u = (strictPrefix t.1 j).1 then
          treeLastLabel u + 1 else 0) htF
      have hjparent : TreeNode.parent t.1 = (strictPrefix t.1 j).1 := hj.1.symm
      change (if TreeNode.parent t.1 = (strictPrefix t.1 j).1 then
        treeLastLabel t.1 + 1 else 0) ≤ _ at hle
      rw [if_pos hjparent] at hle
      exact hle
    have hlarge : treeLastLabel t.1 + 1 ≤ β m (strictPrefix t.1 j) :=
      hsup.trans (le_max_right _ _)
    have hcyl := ht j
    rw [hj.2] at hcyl
    exact (not_lt_of_ge hcyl) (lt_of_lt_of_le (Nat.lt_succ_self _) hlarge)
  have hβtendsto : Tendsto β atTop (nhds α) := by
    rw [tendsto_pi_nhds]
    intro q
    let bad : Set ℕ := {m | ∃ t ∈ F (φ m), TreeNode.parent t = q.1}
    have hbadsub : bad.Subsingleton := by
      intro i hi j hj
      rcases hi with ⟨ti, hti, hpi⟩
      rcases hj with ⟨tj, htj, hpj⟩
      by_contra hij
      have hindices : φ i ≠ φ j := fun h ↦ hij (hφ h)
      have hdis := hF hindices
      have hqmem : q.1 ∈
          TreeNode.parent '' (F (φ i) : Set (TreeNode n)) ∩
            TreeNode.parent '' (F (φ j) : Set (TreeNode n)) := by
        constructor
        · exact ⟨ti, hti, hpi⟩
        · exact ⟨tj, htj, hpj⟩
      rw [hdis] at hqmem
      exact hqmem
    have hevent : ∀ᶠ m in atTop, m ∉ bad := by
      rw [← Nat.cofinite_eq_atTop]
      exact hbadsub.finite.eventually_cofinite_notMem
    have heq : (fun m ↦ β m q) =ᶠ[atTop] fun _ ↦ α q := by
      filter_upwards [hevent] with m hm
      have hsupzero : (F (φ m)).sup (fun t ↦
          if TreeNode.parent t = q.1 then treeLastLabel t + 1 else 0) = 0 := by
        apply le_antisymm
        · apply Finset.sup_le
          intro t ht
          rw [if_neg]
          intro hparent
          exact hm ⟨t, ht, hparent⟩
        · exact bot_le
      simp [β, hsupzero]
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  have hzβ : ∀ m, z (β m) ≤ 0 := by
    intro m
    have hle := hz (φ m) (β m)
    change z (β m) ≤ g (φ m) (β m) at hle
    rw [hgzero m (β m) (hβoutside m)] at hle
    exact hle
  have hzlim : Tendsto (fun m ↦ z (β m)) atTop (nhds (z α)) :=
    Filter.Tendsto.comp z.continuous.continuousAt hβtendsto
  exact isClosed_Iic.mem_of_tendsto hzlim (Eventually.of_forall hzβ)
end OrderClosures
