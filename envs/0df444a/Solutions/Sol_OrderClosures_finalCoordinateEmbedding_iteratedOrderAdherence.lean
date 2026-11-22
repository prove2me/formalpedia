-- Prove2me | solution 1 for OrderClosures.finalCoordinateEmbedding_iteratedOrderAdherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:14:45.885243+00:00
-- url     : https://prove2.me/submissions/96d9ca84-590a-4568-b699-95730169078d

module
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Moderated
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_FinalSpace
public import Theorems.Thm_OrderClosures_finalLatticeNorm_coordinateEmbedding
public import Theorems.Thm_OrderClosures_finalCoordinateEmbedding_orderConverges
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
theorem _root_.solution (n k : ℕ)
    {z : TreeComponent n}
    (hz : z ∈ iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) :
    finalCoordinateEmbedding n z ∈
      iteratedOrderAdherence (unitBallFor finalLatticeNorm) k := by
  induction k generalizing z with
  | zero =>
      change componentLatticeNorm n z ≤ 1 at hz
      change finalLatticeNorm (finalCoordinateEmbedding n z) ≤ 1
      simpa [finalLatticeNorm_coordinateEmbedding] using hz
  | succ k ih =>
      change z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor (componentLatticeNorm n)) k) at hz
      rcases hz with ⟨ι, hpre, hdir, hne, f, hfmem, hfz⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      change finalCoordinateEmbedding n z ∈ orderAdherence
        (iteratedOrderAdherence (unitBallFor finalLatticeNorm) k)
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ finalCoordinateEmbedding n (f i), fun i ↦ ih (hfmem i), ?_⟩
      exact finalCoordinateEmbedding_orderConverges hfz
end OrderClosures
