-- Prove2me | solution 1 for QECCertificates.eq_zero_of_mem_spanL_of_piv_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:46.548104+00:00
-- url     : https://prove2.me/submissions/8702a60e-52a4-4000-8bd1-d7df97a5c1a2

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Theorems.Thm_QECCertificates_readOff_nil
public import Theorems.Thm_QECCertificates_readOff_eq_of_mem_spanL
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_kerL
attribute [local simp] QECCertificates.mem_support
attribute [local simp] QECCertificates.rowReduceFrom_cons
attribute [local simp] QECCertificates.rowReduceFrom_nil


attribute [local simp] QECCertificates.readOff_nil

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) {w : Vec n}
    (hw : w ∈ spanL (rowList D)) (h0 : ∀ ri ∈ D, w ri.2 = 0) : w = 0 := by
  rw [← readOff_eq_of_mem_spanL hD hw]
  simp only [readOff]
  exact Finset.sum_eq_zero fun ri hri => by
    rw [h0 ri (List.mem_toFinset.mp hri), zero_smul]
end QECCertificates
