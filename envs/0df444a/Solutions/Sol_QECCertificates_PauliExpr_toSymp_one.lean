-- Prove2me | solution 1 for QECCertificates.PauliExpr.toSymp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:30.997995+00:00
-- url     : https://prove2.me/submissions/0f33d56c-935e-4d59-9cd2-344f7ece1d6b

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr
public import Theorems.Thm_QECCertificates_Pauli_mul_I_left
public import Theorems.Thm_QECCertificates_Pauli_mul_I_right
public import Theorems.Thm_QECCertificates_Pauli_mul_self
public import Theorems.Thm_QECCertificates_Pauli_anti_self
public import Theorems.Thm_QECCertificates_sympWord_fst
public import Theorems.Thm_QECCertificates_sympWord_snd
public import Theorems.Thm_QECCertificates_commutesWord_self
public import Theorems.Thm_QECCertificates_PauliExpr_eval_one
public import Theorems.Thm_QECCertificates_PauliExpr_eval_mul
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


attribute [local simp] QECCertificates.Pauli.mul_I_left
attribute [local simp] QECCertificates.Pauli.mul_I_right
attribute [local simp] QECCertificates.Pauli.mul_self
attribute [local simp] QECCertificates.Pauli.anti_self
attribute [local simp] QECCertificates.sympWord_fst
attribute [local simp] QECCertificates.sympWord_snd
attribute [local simp] QECCertificates.commutesWord_self
attribute [local simp] QECCertificates.PauliExpr.eval_one
attribute [local simp] QECCertificates.PauliExpr.eval_mul

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr
namespace QECCertificates.PauliExpr
theorem _root_.solution : toSymp (.one : PauliExpr n) = 0 := by
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [toSymp, sympWord, Pauli.symp]
end QECCertificates.PauliExpr
