-- Prove2me | solution 1 for QECCertificates.Pauli.mul_I_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:51.166283+00:00
-- url     : https://prove2.me/submissions/0537f42a-851f-4b64-aca8-bea9b8a7e6fe

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
theorem _root_.solution (p : Pauli) : mul .I p = p := by cases p <;> rfl
end QECCertificates.Pauli
