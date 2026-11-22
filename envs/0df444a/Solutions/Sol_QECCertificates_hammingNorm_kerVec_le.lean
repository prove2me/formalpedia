-- Prove2me | solution 1 for QECCertificates.hammingNorm_kerVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:52:43.949907+00:00
-- url     : https://prove2.me/submissions/7a14f1e6-0461-4130-ada4-892454ecaedf

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_pivCols
public import Theorems.Thm_QECCertificates_kerVec_apply_free
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_weight_eq_hammingNorm
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.mem_kerL

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (D : List (PivRow n)) (j : Fin n) :
    hammingNorm (kerVec D j) ≤ D.length + 1 := by
  rw [← weight_eq_hammingNorm]
  calc (support (kerVec D j)).card
      ≤ (insert j (pivCols D)).card := Finset.card_le_card (fun i hi => ?_)
    _ ≤ (pivCols D).card + 1 := Finset.card_insert_le j (pivCols D)
    _ ≤ D.length + 1 := by
        have h := List.toFinset_card_le (D.map (·.2))
        simp only [pivCols, List.length_map] at h ⊢
        omega
  rw [support, Finset.mem_filter] at hi
  obtain ⟨-, hne⟩ := hi
  rw [Finset.mem_insert, mem_pivCols]
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hij, hnot⟩ := hcon
  have hfree : IsFreeCol D i := fun ri hri hcon2 => hnot ⟨ri, hri, hcon2⟩
  rw [kerVec_apply_free hfree, if_neg hij] at hne
  exact hne rfl
end QECCertificates
