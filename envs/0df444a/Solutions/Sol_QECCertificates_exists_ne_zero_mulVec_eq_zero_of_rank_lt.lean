-- Prove2me | solution 1 for QECCertificates.exists_ne_zero_mulVec_eq_zero_of_rank_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:45.965483+00:00
-- url     : https://prove2.me/submissions/3271d48a-92ad-4afc-9d85-81b751b39f1a

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_nodupPiv_rowReduce
public import Theorems.Thm_QECCertificates_card_pivCols_eq_length
public import Theorems.Thm_QECCertificates_Matrix_rank_eq_length_rowReduce
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_exists_light_mem_kerL
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_pivCols
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : M.rank < n) : ∃ v : Vec n, M *ᵥ v = 0 ∧ v ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin n, IsFreeCol (rowReduce (List.ofFn fun i => M i)) j := by
    by_contra hcon
    have hall : pivCols (rowReduce (List.ofFn fun i => M i)) = Finset.univ := by
      refine Finset.eq_univ_of_forall fun j => ?_
      by_contra hj
      exact hcon ⟨j, fun ri hri heq => hj (mem_pivCols.mpr ⟨ri, hri, heq⟩)⟩
    have hcard := card_pivCols_eq_length (nodupPiv_rowReduce (List.ofFn fun i => M i))
    rw [hall, Finset.card_univ, Fintype.card_fin] at hcard
    rw [Matrix.rank_eq_length_rowReduce] at h
    omega
  obtain ⟨v, hv, hvne, -⟩ := exists_light_mem_kerL (List.ofFn fun i => M i) hj
  refine ⟨v, ?_, hvne⟩
  have hrow : ∀ i : Fin m, (fun j => M i j) ∈ List.ofFn (fun i => M i) := by
    intro i
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  funext i
  have hdot : (fun j => M i j) ⬝ᵥ v = 0 := (mem_kerL.mp hv) _ (hrow i)
  simpa [Matrix.mulVec] using hdot
end QECCertificates
