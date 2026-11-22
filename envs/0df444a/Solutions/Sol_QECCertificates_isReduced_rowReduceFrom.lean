-- Prove2me | solution 1 for QECCertificates.isReduced_rowReduceFrom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:54.091699+00:00
-- url     : https://prove2.me/submissions/287de7c1-94f8-441c-846e-f8bd074c76cd

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Theorems.Thm_QECCertificates_isReduced_step
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.rowReduceFrom_cons

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution {D : List (PivRow n)} (hD : IsReduced D) (rest : List (Vec n)) :
    IsReduced (rowReduceFrom D rest) := by
  induction rest generalizing D with
  | nil => exact hD
  | cons v rest ih => rw [rowReduceFrom_cons]; exact ih (isReduced_step hD v)
end QECCertificates
