-- Prove2me | solution 1 for OrderClosures.solovayLE_eq_sInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:06:24.822576+00:00
-- url     : https://prove2.me/submissions/69a1519d-a2b6-4858-8474-4b97adbdadf5

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
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]
namespace OrderClosures
theorem _root_.solution (n : ℕ) (eta : Gamma) :
    solovayLE Gamma n eta = sInf (Set.range fun m ↦ solovayC Gamma m n eta) := by
  apply le_antisymm
  · apply le_sInf
    intro U hU
    rcases hU with ⟨m, rfl⟩
    change (⟨{f : SolovayProduct Gamma | f n ≤ eta}, _⟩ :
      TopologicalSpace.Opens (SolovayProduct Gamma)) ≤
        ⟨{f : SolovayProduct Gamma | f m < f n → f m < eta}, _⟩
    intro f hf hmn
    exact hmn.trans_le hf
  · let W : TopologicalSpace.Opens (SolovayProduct Gamma) :=
      (sInf (Set.range fun m ↦ solovayC Gamma m n eta) :
        RegularOpen (SolovayProduct Gamma))
    change W ≤ ⟨{f : SolovayProduct Gamma | f n ≤ eta}, _⟩
    intro g hg
    change g n ≤ eta
    by_contra hgn
    have hetagn : eta < g n := lt_of_not_ge hgn
    rcases isOpen_pi_iff.mp W.2 g hg with ⟨F, v, hv, hvW⟩
    obtain ⟨m, hm⟩ := (insert n F).exists_nat_subset_range
    have hmF : m ∉ F := by
      intro hmF
      exact (Nat.lt_irrefl m)
        (Finset.mem_range.mp (hm (Finset.mem_insert_of_mem hmF)))
    have hmn : m ≠ n := by
      intro hmn
      subst n
      exact (Nat.lt_irrefl m)
        (Finset.mem_range.mp (hm (Finset.mem_insert_self m F)))
    let h : SolovayProduct Gamma := fun i ↦ if i = m then eta else g i
    have hhF : h ∈ (F : Set ℕ).pi v := by
      intro i hi
      rw [show h i = g i by simp [h, ne_of_mem_of_not_mem hi hmF]]
      exact (hv i (Finset.mem_coe.mp hi)).2
    have hhW : h ∈ W := hvW hhF
    have hhC : h ∈ (solovayC Gamma m n eta :
        TopologicalSpace.Opens (SolovayProduct Gamma)) :=
      (show sInf (Set.range fun k ↦ solovayC Gamma k n eta) ≤
          solovayC Gamma m n eta from sInf_le (Set.mem_range_self m)) hhW
    change h m < h n → h m < eta at hhC
    have hhm : h m = eta := by simp [h]
    have hhn : h n = g n := by simp [h, hmn.symm]
    have hhless : h m < h n := by simpa only [hhm, hhn] using hetagn
    have hout := hhC hhless
    rw [hhm] at hout
    exact (lt_irrefl eta) hout
end OrderClosures
