-- Prove2me | solution 1 for QECCertificates.spanL_rowList_rowReduceFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:52.465824+00:00
-- url     : https://prove2.me/submissions/0bfa3ff7-7948-4be7-9536-927f4ae686b7

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_spanL_rowList_step
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_spanL_append
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
theorem _root_.solution (D : List (PivRow n)) (rest : List (Vec n)) :
    spanL (rowList (rowReduceFrom D rest)) = spanL (rowList D ++ rest) := by
  induction rest generalizing D with
  | nil => simp
  | cons v rest ih =>
      rw [rowReduceFrom_cons, ih]
      have hassoc : rowList D ++ (v :: rest) = (rowList D ++ [v]) ++ rest := by
        rw [List.append_assoc]; rfl
      rw [hassoc, spanL_append, spanL_append, spanL_rowList_step]
end QECCertificates
