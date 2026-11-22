-- Prove2me | solution 1 for QECCertificates.finrank_spanL_eq_length_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:32.738524+00:00
-- url     : https://prove2.me/submissions/1234cc65-0ade-4e2e-826a-083855687f0e

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Theorems.Thm_QECCertificates_linearIndependent_rowList_of_isReduced
public import Theorems.Thm_QECCertificates_range_get_eq_rowList
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



set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D)
    (hnd : NodupPiv D) :
    Module.finrank (ZMod 2) (spanL (rowList D)) = D.length := by
  have hcard := finrank_span_eq_card (linearIndependent_rowList_of_isReduced hD hnd)
  rw [range_get_eq_rowList] at hcard
  have hcard' : Module.finrank (ZMod 2) (spanL (rowList D)) = Fintype.card (Fin D.length) :=
    hcard
  simpa [Fintype.card_fin] using hcard'
end QECCertificates
