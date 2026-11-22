-- Prove2me | solution 1 for QECCertificates.spanL_rowReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:54.866719+00:00
-- url     : https://prove2.me/submissions/f640828c-2089-4c3e-9243-420ee8be3e51

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_spanL_rowList_rowReduceFrom
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.rowReduceFrom_nil
attribute [local simp] QECCertificates.rowReduceFrom_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (L : List (Vec n)) : spanL (rowList (rowReduce L)) = spanL L := by
  have h := spanL_rowList_rowReduceFrom ([] : List (PivRow n)) L
  simpa [rowReduce] using h
end QECCertificates
