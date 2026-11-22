-- Prove2me | solution 1 for QECCertificates.Pauli.mul_I_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:49:55.651339+00:00
-- url     : https://prove2.me/submissions/7eb935d4-eedd-4a42-9d88-f4e082c398e3

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
theorem _root_.solution (p : Pauli) : mul p .I = p := by cases p <;> rfl
end QECCertificates.Pauli
