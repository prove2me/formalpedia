-- Prove2me | solution 1 for QECCertificates.kerVec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:10.897468+00:00
-- url     : https://prove2.me/submissions/0ed2b7c7-5dd4-4a9c-913f-aed369f508ac

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Theorems.Thm_QECCertificates_mem_kerL
public import Theorems.Thm_QECCertificates_kerVec_apply_free
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
public import Theorems.Thm_QECCertificates_rowReduceFrom_cons
public import Theorems.Thm_QECCertificates_rowReduceFrom_nil
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
theorem _root_.solution {D : List (PivRow n)} {j : Fin n} (hj : IsFreeCol D j) :
    kerVec D j ≠ 0 := by
  intro hzero
  have h1 : kerVec D j j = 1 := by rw [kerVec_apply_free hj, if_pos rfl]
  rw [hzero] at h1
  simp only [Pi.zero_apply] at h1
  exact zero_ne_one h1
end QECCertificates
