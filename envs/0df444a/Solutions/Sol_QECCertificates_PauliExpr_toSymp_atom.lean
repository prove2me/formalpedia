-- Prove2me | solution 1 for QECCertificates.PauliExpr.toSymp_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:20.211777+00:00
-- url     : https://prove2.me/submissions/dcad327e-88d7-4fa9-a579-b3ef6e749b70

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
public import Theorems.Thm_QECCertificates_PauliExpr_toSymp_one
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
attribute [local simp] QECCertificates.PauliExpr.toSymp_one

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.PauliExpr
namespace QECCertificates.PauliExpr
theorem _root_.solution (i : Fin n) (p : Pauli) :
    toSymp (.atom i p)
      = ((fun j => if j = i then (Pauli.symp p).1 else 0),
         (fun j => if j = i then (Pauli.symp p).2 else 0)) := by
  refine Prod.ext ?_ ?_ <;> funext j <;>
    · simp only [toSymp, sympWord, eval]
      by_cases h : j = i <;> simp [h, Pauli.symp]
end QECCertificates.PauliExpr
