-- Prove2me | solution 1 for OrderClosures.finalCoordinateEmbedding_orderConverges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:38.208259+00:00
-- url     : https://prove2.me/submissions/9aa1fe71-2190-4f70-8cc5-fd00e855aedb

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
public import Theorems.Thm_OrderClosures_finalCoordinateEmbedding_ne
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
    {n : ℕ} {ι : Type} [Preorder ι] {f : ι → TreeComponent n} {z : TreeComponent n}
    (hf : OrderConvergesTo f z) :
    OrderConvergesTo (fun i ↦ finalCoordinateEmbedding n (f i))
      (finalCoordinateEmbedding n z) := by
  classical
  rcases hf with ⟨κ, hκpre, hκdir, hκne, r, hranti, hrpos, hrglb, hcontrol⟩
  let : Preorder κ := hκpre
  let : IsDirected κ (· ≤ ·) := hκdir
  let : Nonempty κ := hκne
  refine ⟨κ, inferInstance, inferInstance, inferInstance,
    fun k ↦ finalCoordinateEmbedding n (r k), ?_, ?_, ?_, ?_⟩
  · intro a b hab m
    by_cases hmn : m = n
    · subst m
      simpa using hranti hab
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · intro k m
    by_cases hmn : m = n
    · subst m
      simpa using hrpos k
    · simp [finalCoordinateEmbedding_ne n m hmn]
  · constructor
    · rintro _ ⟨k, rfl⟩
      intro m
      by_cases hmn : m = n
      · subst m
        simpa using hrpos k
      · simp [finalCoordinateEmbedding_ne n m hmn]
    · intro y hy m
      by_cases hmn : m = n
      · subst m
        apply hrglb.2
        rintro _ ⟨k, rfl⟩
        simpa using hy ⟨k, rfl⟩ n
      · let k₀ : κ := Classical.choice inferInstance
        have := hy ⟨k₀, rfl⟩ m
        simpa [finalCoordinateEmbedding_ne n m hmn] using this
  · intro k
    filter_upwards [hcontrol k] with i hi
    intro m
    by_cases hmn : m = n
    · subst m
      change |(finalCoordinateEmbedding n (f i)).1 n -
          (finalCoordinateEmbedding n z).1 n| ≤
        (finalCoordinateEmbedding n (r k)).1 n
      simpa using hi
    · change |(finalCoordinateEmbedding n (f i)).1 m -
          (finalCoordinateEmbedding n z).1 m| ≤
        (finalCoordinateEmbedding n (r k)).1 m
      rw [finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn,
        finalCoordinateEmbedding_ne n m hmn]
      simp
end OrderClosures
