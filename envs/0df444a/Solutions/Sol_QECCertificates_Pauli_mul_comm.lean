-- Prove2me | solution 1 for QECCertificates.Pauli.mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:23:04.343137+00:00
-- url     : https://prove2.me/submissions/7f4003f5-5715-4a60-901a-cf0a574956c9

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
theorem _root_.solution (p q : Pauli) : mul p q = mul q p := by fin_cases p <;> fin_cases q <;> rfl
end QECCertificates.Pauli
