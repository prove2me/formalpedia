-- Prove2me | solution 1 for QECCertificates.Pauli.mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:58.962858+00:00
-- url     : https://prove2.me/submissions/051026e4-cdcd-4eb7-9848-45a94b8e03ee

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_Pauli_Expr

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}
open QECCertificates.Pauli
namespace QECCertificates.Pauli
theorem _root_.solution (p : Pauli) : mul p p = .I := by cases p <;> rfl
end QECCertificates.Pauli
