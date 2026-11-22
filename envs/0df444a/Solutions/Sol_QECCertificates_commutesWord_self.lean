-- Prove2me | solution 1 for QECCertificates.commutesWord_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:50:04.966339+00:00
-- url     : https://prove2.me/submissions/31f21a44-e9e7-4751-882b-553859566853

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
public import Theorems.Thm_QECCertificates_Pauli_anti_self
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


attribute [local simp] QECCertificates.Pauli.anti_self

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
namespace QECCertificates
theorem _root_.solution (u : PauliWord n) : commutesWord u u := by
  rw [commutesWord]
  exact Finset.sum_eq_zero fun i _ => Pauli.anti_self (u i)
end QECCertificates
