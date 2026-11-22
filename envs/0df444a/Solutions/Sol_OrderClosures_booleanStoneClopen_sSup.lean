-- Prove2me | solution 1 for OrderClosures.booleanStoneClopen_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:07.352343+00:00
-- url     : https://prove2.me/submissions/43d4b303-beb1-4361-a86b-8957b3cc431c

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
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
open Set
noncomputable section
open OrderClosures
universe u
variable (B : Type u) [CompleteBooleanAlgebra B]
namespace OrderClosures
theorem _root_.solution (S : Set B) :
    booleanStoneClopen B (sSup S) =
      closure (⋃ b ∈ S, booleanStoneClopen B b) := by
  apply Set.Subset.antisymm
  · intro x hxs
    by_contra hxclosure
    have hxopen : x ∈ (closure (⋃ b ∈ S, booleanStoneClopen B b))ᶜ :=
      hxclosure
    rcases booleanStone_clopen_basis B (isOpen_compl_iff.mpr isClosed_closure)
        hxopen with ⟨d, hxd, hd⟩
    have hsd : sSup S ≤ dᶜ := by
      apply sSup_le
      intro b hbS
      apply (booleanStoneClopen_subset_iff B).mp
      intro y hyb
      rw [booleanStoneClopen_compl]
      intro hyd
      have hyunion : y ∈ ⋃ c ∈ S, booleanStoneClopen B c := by
        simp only [Set.mem_iUnion]
        exact ⟨b, hbS, hyb⟩
      exact (hd hyd) (subset_closure hyunion)
    have hxcomp : x ∈ booleanStoneClopen B dᶜ :=
      (booleanStoneClopen_subset_iff B).mpr hsd hxs
    rw [booleanStoneClopen_compl] at hxcomp
    exact hxcomp hxd
  · apply closure_minimal
    · intro x hx
      simp only [Set.mem_iUnion] at hx
      rcases hx with ⟨b, hbS, hxb⟩
      exact (booleanStoneClopen_subset_iff B).mpr (le_sSup hbS) hxb
    · exact (isClopen_booleanStoneClopen B (sSup S)).1
end OrderClosures
