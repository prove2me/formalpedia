-- Prove2me | solution 1 for OrderClosures.iteratedOrderAdherence_mono_and_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:54.263648+00:00
-- url     : https://prove2.me/submissions/3ac03087-af43-4699-bda6-dce69bad9228

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Definitions.Def_LeanPool_OrderClosures_WeaklyFatou_Reductions
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
public import Theorems.Thm_OrderClosures_orderAdherence_mono
public import Theorems.Thm_OrderConvergesTo_smul
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
variable {X : Type u} [AddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [VectorLattice X]
namespace OrderClosures
theorem _root_.solution
    {A B : Set X} {c : ℝ} (hc : 0 < c) :
    (A ⊆ B → ∀ m, iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m) ∧
      (orderAdherence (scaleSet c A) = scaleSet c (orderAdherence A) ∧
        ∀ m, iteratedOrderAdherence (scaleSet c A) m =
          scaleSet c (iteratedOrderAdherence A m)) := by
  have hmono : A ⊆ B → ∀ m,
      iteratedOrderAdherence A m ⊆ iteratedOrderAdherence B m := by
    intro hAB m
    induction m with
    | zero => exact hAB
    | succ m ih => exact orderAdherence_mono ih
  have hscale : ∀ C : Set X,
      orderAdherence (scaleSet c C) = scaleSet c (orderAdherence C) := by
    intro C
    apply Set.Subset.antisymm
    · rintro x ⟨ι, hpre, hdir, hne, f, hf, hfx⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      refine ⟨c⁻¹ • x, ?_, by simp [smul_smul, hc.ne']⟩
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c⁻¹ • f i, ?_, ?_⟩
      · intro i
        rcases hf i with ⟨a, ha, hfa⟩
        change c⁻¹ • f i ∈ C
        rw [← hfa]
        simpa [smul_smul, hc.ne'] using ha
      · exact hfx.smul c⁻¹
    · rintro x ⟨y, ⟨ι, hpre, hdir, hne, f, hf, hfy⟩, rfl⟩
      let : Preorder ι := hpre
      let : IsDirected ι (· ≤ ·) := hdir
      let : Nonempty ι := hne
      refine ⟨ι, inferInstance, inferInstance, inferInstance,
        fun i ↦ c • f i, ?_, hfy.smul c⟩
      exact fun i ↦ ⟨f i, hf i, rfl⟩
  have hiter : ∀ m, iteratedOrderAdherence (scaleSet c A) m =
      scaleSet c (iteratedOrderAdherence A m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        simpa only [iteratedOrderAdherence, ih] using
          hscale (iteratedOrderAdherence A m)
  exact ⟨hmono, hscale A, hiter⟩
end OrderClosures
